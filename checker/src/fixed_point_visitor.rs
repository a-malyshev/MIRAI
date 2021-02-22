// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use crate::abstract_value::{AbstractValue, AbstractValueTrait};
use crate::block_visitor::BlockVisitor;
use crate::body_visitor::BodyVisitor;
use crate::environment::Environment;
use crate::options::DiagLevel;
use crate::{abstract_value, k_limits};
use itertools::Itertools;
use crate::path::*;
use log_derive::*;
use mirai_annotations::*;
use rpds::{HashTrieMap, HashTrieSet};
use rustc_data_structures::graph::dominators::Dominators;
use rustc_middle::mir;
use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Formatter, Result};
use std::rc::Rc; 
use crate::interval_domain::{self, IntervalDomain};

use crate::constant_domain::ConstantDomain;
use crate::expression::{Expression};

pub struct FixedPointVisitor<'fixed, 'analysis, 'compilation, 'tcx, E> {
    pub bv: &'fixed mut BodyVisitor<'analysis, 'compilation, 'tcx, E>,
    already_visited: HashTrieSet<mir::BasicBlock>,
    pub block_indices: Vec<mir::BasicBlock>,
    guard: Rc<AbstractValue>,
    contin: bool,
    loop_anchors: HashSet<mir::BasicBlock>,
    dominators: Dominators<mir::BasicBlock>,
    in_state: HashMap<mir::BasicBlock, Environment>,
    out_state: HashMap<mir::BasicBlock, Environment>,
    pub terminator_state: HashMap<mir::BasicBlock, Environment>,
}

impl<'fixed, 'analysis, 'compilation, 'tcx, E> Debug
    for FixedPointVisitor<'fixed, 'analysis, 'compilation, 'tcx, E>
{
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        "FixedPoint".fmt(f)
    }
}

/// A visitor that simply traverses enough of the MIR associated with a particular code body
/// so that we can test a call to every default implementation of the MirVisitor trait.
impl<'fixed, 'analysis, 'compilation, 'tcx, E>
    FixedPointVisitor<'fixed, 'analysis, 'compilation, 'tcx, E>
{
    #[logfn_inputs(TRACE)]
    pub fn new(
        body_visitor: &'fixed mut BodyVisitor<'analysis, 'compilation, 'tcx, E>,
    ) -> FixedPointVisitor<'fixed, 'analysis, 'compilation, 'tcx, E> {
        let dominators = body_visitor.mir.dominators();
        let (block_indices, loop_anchors) = get_sorted_block_indices(body_visitor.mir, &dominators);
        // in_state[bb] is the join (or widening) of the out_state values of each predecessor of bb
        let mut in_state: HashMap<mir::BasicBlock, Environment> = HashMap::new();
        // out_state[bb] is the environment that results from analyzing block bb, given in_state[bb]
        let mut out_state: HashMap<mir::BasicBlock, Environment> = HashMap::new();
        // terminator_state[bb] is the environment that should be used to error check the terminator of bb
        let mut terminator_state: HashMap<mir::BasicBlock, Environment> = HashMap::new();
        for bb in block_indices.iter() {
            in_state.insert(*bb, Environment::default());
            out_state.insert(*bb, Environment::default());
            terminator_state.insert(*bb, Environment::default());
        }
        FixedPointVisitor {
            already_visited: HashTrieSet::new(),
            bv: body_visitor,
            block_indices,
            guard: Rc::new(abstract_value::BOTTOM),
            contin: true,
            loop_anchors,
            dominators,
            in_state,
            out_state,
            terminator_state,
        }
    }

    /// Visits each statement in order and then visits the terminator.
    #[logfn_inputs(TRACE)]
    pub fn visit_blocks(&mut self) {
        let blocks = self.block_indices.clone();
        for bb in blocks {
            check_for_early_break!(self.bv);
            if !self.already_visited.contains(&bb) {
                if !self.loop_anchors.contains(&bb) {
                    self.visit_basic_block(bb, 0);
                } else {
                    self.compute_fixed_point(bb);
                }
            }
        }
    }

    fn bind_with_guard(&self, bb: &mir::BasicBlock, variables: &HashSet<Rc<Path>>) {
        for key in variables.iter() {
            let val = self.in_state[bb].value_map.get(key);
            let right_bound = AbstractValue::make_from(
                Expression::CompileTimeConstant(ConstantDomain::I128(8)),
                1
            );
            let val = if let Some(val) = val {
                val.extend_od(right_bound)
            } else { Rc::new(abstract_value::BOTTOM) };
            println!("var name is {:?}, {:?}", key, val.octagon);
        }
    }

    fn check_loop_cond(&self, 
            x_interval: &IntervalDomain, 
            threshold_interval: &IntervalDomain, 
            expr: &'static str,
        ) -> bool {
        if expr == "LE" {
            if let Some(upper_bound) = x_interval.upper_bound() {
                if upper_bound >= threshold_interval.upper_bound().unwrap() { 
                    println!("ouch! stopping here");
                    //i_state.entry_condition = self.in_state[&bb].entry_condition.clone();
                    //i_state.entry_condition =  Rc::new(abstract_value::FALSE);
                    return false;
                } 
            }
        } else if expr == "LT" {
            if let Some(upper_bound) = x_interval.upper_bound() {
                if upper_bound >= threshold_interval.upper_bound().unwrap() { 
                    println!("ouch! stopping here");
                    //i_state.entry_condition = self.in_state[&bb].entry_condition.clone();
                    //i_state.entry_condition =  Rc::new(abstract_value::FALSE);
                    return false;
                } 
            }
        } else if expr == "GE" {
            if let Some(lower_bound) = x_interval.lower_bound() {
                if lower_bound <= threshold_interval.upper_bound().unwrap() { 
                    println!("ouch! stopping here");
                    //i_state.entry_condition = self.in_state[&bb].entry_condition.clone();
                    //i_state.entry_condition =  Rc::new(abstract_value::FALSE);
                    return false;
                } 
            }
        } else if expr == "GT" {
            if let Some(lower_bound) = x_interval.lower_bound() {
                if lower_bound <= threshold_interval.upper_bound().unwrap() { 
                    println!("ouch! stopping here");
                    //i_state.entry_condition = self.in_state[&bb].entry_condition.clone();
                    //i_state.entry_condition =  Rc::new(abstract_value::FALSE);
                    return false;
                } 
            }
        }
        return true;
    }

    /// Visits a single basic block, starting with an in_state that is the join of all of
    /// the out_state values of its predecessors and then updating out_state with the final
    /// current_environment of the block. Also adds the block to the already_visited set.
    #[logfn_inputs(TRACE)]
    fn visit_basic_block(&mut self, bb: mir::BasicBlock, iteration_count: usize) {
        // Merge output states of predecessors of bb
        let mut i_state = if iteration_count == 0 && bb.index() == 0 {
            self.bv.first_environment.clone()
        } else {
            self.get_initial_state_from_predecessors(bb, iteration_count)
        };
        //println!("--- iter cont: {:?}", iteration_count);
        //let map = self.out_state[&bb].value_map.clone();
        //let discr = self.get_discr_val(bb, &map);
        //let cond = AbstractValue::make_from(
            //Expression::CompileTimeConstant(ConstantDomain::False),
            //1
        //);
        //if let Expression::LessOrEqual{left, right} = &discr.expression {
            //println!("===========yep, good: {:?}", right);
            //let result = discr.equals(cond);
            //println!("****** result: {:?}", result);
            //if Rc::new(abstract_value::TRUE) == result {
                //println!("ouch! stopping here");
                //return;
            //}
            //let interval = left.get_as_interval();
            //println!("nope, another try: here is the left side {:?}", interval);
            //if interval.upper_bound() > right.get_as_interval().upper_bound() {
                //println!("ouch. v2! stopping here");
                //return;
            //}

        //} else {
            //println!("===========no, bad: {:?}", discr.expression);
        //}
   

        //println!("size of exit cond: {}", self.in_state[&bb].exit_conditions.size());
        //for (_bb, ex) in self.in_state[&bb].exit_conditions.iter() {
            //println!("----- exit cond is {:?} for bb: {:?}", ex, _bb);
        //}
        //println!("----- 2. exit cond is {:?}", self.out_state[&bb].exit_conditions.get(&bb));
        // Note that iteration_count is zero unless bb is a loop anchor.


        //let mut contin = true;
        if iteration_count >= 2 {
            if let Some((p, threshold, expr)) = &self.bv.guard {
                //let x = self.in_state[&bb].value_map.get(p);
                let x = self.in_state[&bb].value_map.get(p);
                println!("--- iteration #{:?}, x value is {:?}", iteration_count, x);
                if let Some(x_val) = x {
                    let x_interval = x_val.get_as_interval();
                    let threshold_interval = &threshold.get_as_interval();
                    //TODO: it will only work for the cases where loop condition is x <= or < some
                    //constant
                    println!("checking loop condition: {:?} and {:?}", x_interval, threshold_interval);
                    self.contin = self.check_loop_cond(&x_interval, &threshold_interval, expr);
                }
            }
        }

        //if contin && (iteration_count >= 2 && iteration_count <= 8) {
        if self.contin && iteration_count != 0 && iteration_count != 1 && iteration_count <= 8 {

            // We do not have (and don't want to have) a way to distinguish the value of a widened
            // loop variable in one iteration from its value in the previous iteration, so
            // conditions involving loop variables are not referentially transparent
            // and we have to do without them. Also, only the conditions that flow into
            // the loop anchor at iteration 1 (i.e. before the loop body was executed the first time)
            // can be loop invariant (and thus apply to all executions of the loop body).
            let loop_variants = self.in_state[&bb].get_loop_variants(&i_state);
            
            //println!("state: {:?}", self.in_state[&bb]);
            // iterate over these variables and bind with Loop Guard
            //self.guard
            //self.bind_with_guard(&bb, &loop_variants);

            let previous_state = &self.in_state[&bb];
            let invariant_entry_condition = previous_state
                .entry_condition
                .remove_conjuncts_that_depend_on(&loop_variants);
            //println!("exit cond is {:?}", previous_state.entry_condition);
            //println!("inv entry cond is {:?}", invariant_entry_condition);
            i_state = if iteration_count == 2 {
                println!("joining...");
                previous_state.join(i_state)
            } else {
                //println!("widening...");
                println!("joining...");
                //previous_state.widen(i_state, &self.bv.guard)
                previous_state.join(i_state)
            };
            println!("------- num iter: {:?}", i_state.num_iter);
            i_state.entry_condition = invariant_entry_condition;
        } else if self.contin && iteration_count > 8 {
            // From iteration 3 onwards, the entry condition is not affected by changes in the loop
            // body, so we just stick to the one computed in iteration 3.
            println!("********here we go: {}", iteration_count);
            let invariant_entry_condition = self.in_state[&bb].entry_condition.clone();
            println!("widening...");
            i_state = self.in_state[&bb].widen(i_state, &self.bv.guard);
            //i_state = self.in_state[&bb].join(i_state);
            i_state.entry_condition = invariant_entry_condition;
        }
        self.in_state.insert(bb, i_state.clone());
        self.bv.current_environment = i_state;
        let mut block_visitor = BlockVisitor::new(self.bv);
        block_visitor.visit_basic_block(bb, &mut self.terminator_state);
        self.out_state
            .insert(bb, self.bv.current_environment.clone());
        self.already_visited.insert_mut(bb);
    }

    /// Repeatedly evaluate the loop body starting at loop_anchor until widening
    /// kicked in and a fixed point has been reached.
    #[logfn_inputs(TRACE)]
    fn compute_fixed_point(&mut self, loop_anchor: mir::BasicBlock) -> mir::BasicBlock {
        let saved_already_visited = self.already_visited.clone();
        let saved_fresh_variable_offset = self.bv.fresh_variable_offset;
        let mut iteration_count = 1;
        let mut changed = true;
        let mut last_block = loop_anchor;
        // Iterate at least 4 times so that widening kicks in for loop variables and at least
        // two iterations were performed starting with widened variables.
        while iteration_count <= 4 || changed {
            self.already_visited = saved_already_visited.clone();
            self.bv.fresh_variable_offset = saved_fresh_variable_offset;
            let result = self.visit_loop_body(loop_anchor, iteration_count);
            changed = result.0;
            last_block = result.1;
            check_for_early_break!(self.bv);
            if iteration_count >= k_limits::MAX_FIXPOINT_ITERATIONS {
                break;
            }
            iteration_count += 1;
        }
        if iteration_count >= k_limits::MAX_FIXPOINT_ITERATIONS {
            if changed {
                if self.bv.cv.options.diag_level == DiagLevel::PARANOID {
                    let span = self.bv.current_span;
                    let error = self.bv.cv.session.struct_span_err(
                        span,
                        &format!(
                            "Fixed point loop iterations exceeded limit of {}",
                            k_limits::MAX_FIXPOINT_ITERATIONS
                        ),
                    );
                    self.bv.emit_diagnostic(error);
                } else {
                    warn!(
                        "Fixed point loop iterations {} exceeded limit of {} at {:?} in function {}.",
                        iteration_count,
                        k_limits::MAX_FIXPOINT_ITERATIONS,
                        self.bv.current_span,
                        self.bv.function_name
                    );
                }
            } else {
                trace!(
                    "Fixed point loop iterations {} exceeded limit of {} at {:?} in function {}.",
                    iteration_count,
                    k_limits::MAX_FIXPOINT_ITERATIONS,
                    self.bv.current_span,
                    self.bv.function_name
                );
            }
        }
        last_block
    }

    fn get_discr_val<'a>(&mut self, bb: mir::BasicBlock, value_map: &'a HashTrieMap<Rc<Path>, Rc<AbstractValue>>) -> Rc<AbstractValue> {
        let mir::BasicBlockData { ref terminator, .. } = &self.bv.mir[bb];
        if let Some(mir::Terminator { ref kind, .. }) = *terminator {
            return self.fun(kind, bb, value_map);
        }
        Rc::new(abstract_value::BOTTOM)
    }

    fn fun<'a>(&mut self, kind: &mir::TerminatorKind<'tcx>, bb: mir::BasicBlock, value_map: &'a HashTrieMap<Rc<Path>, Rc<AbstractValue>>) -> Rc<AbstractValue> {
        if let mir::TerminatorKind::SwitchInt { discr, .. } = kind {
            let val = self.operand_to_path(bb, discr, value_map);
            println!("switch int. Disrc: {:?}, kind: {:?}, abstr.val: {:?}", discr, kind, val);
            return val.unwrap_or(&Rc::new(abstract_value::BOTTOM)).clone();
        }
        Rc::new(abstract_value::BOTTOM)
    }

    fn operand_to_path<'a>(
        &mut self,
        bb: mir::BasicBlock,
        op: &rustc_middle::mir::Operand<'tcx>,
        value_map: &'a HashTrieMap<Rc<Path>, Rc<AbstractValue>>
    ) -> Option<&'a Rc<AbstractValue>> {
        let mut block_visitor = BlockVisitor::new(self.bv);
        //for v in value_map1.iter() {
            //let path = v.0;
        //if let PathEnum::LocalVariable { ordinal } = path.value {
            // TODO: how to design it?
        match op {
            mir::Operand::Copy(place) 
            | mir::Operand::Move(place) => {
                let p = block_visitor.visit_place(&place);
                println!("operand is {:?}, place: {:?}, path: {:?}", op, place, p);
                let val = value_map.get(&p);
                return val.clone();
            }, 
            _ => return None,
        };
    }

    /// Visits a loop body. Return true if the out_state computed by this visit is not a subset
    /// of the out_state computed previously. When it is a subset, a fixed point has been reached.
    /// A loop body is all of the blocks that are dominated by the loop anchor.
    #[logfn_inputs(TRACE)]
    fn visit_loop_body(
        &mut self,
        loop_anchor: mir::BasicBlock,
        iteration_count: usize,
    ) -> (bool, mir::BasicBlock) {
        let mut changed = false;
        let mut last_block = loop_anchor;
        let blocks = self.block_indices.clone();
        let old_state = self.out_state.clone();
        for bb in blocks {
            if !self.already_visited.contains(&bb)
                && self.dominators.is_dominated_by(bb, loop_anchor)
            {
                last_block = bb;

                //self.guard = self.get_discr_val(bb);
                //println!("guard: {:?}", self.guard);
                

                //let cond = self.guard.less_than(AbstractValue::make_from(
                            //Expression::CompileTimeConstant(ConstantDomain::I128(0)),
                            //1
                //));
                //let cond2 = self.guard.greater_than(AbstractValue::make_from(
                            //Expression::CompileTimeConstant(ConstantDomain::I128(0)),
                            //1
                //));
                //let cond = AbstractValue::make_from(
                            //Expression::CompileTimeConstant(ConstantDomain::False),
                            //1
                //);
                //let mut pred = self.bv.smt_solver.get_as_smt_predicate(&cond.expression);
                //let mut pred2 = self.bv.smt_solver.get_as_smt_predicate(&cond2.expression);
                //let expr = self.bv.smt_solver.solve_expression(&mut pred);
                //let expr2 = self.bv.smt_solver.solve_expression(&mut pred2);
                //println!("discr is {:?}", self.guard);
                //println!("interval value is {:?}, {:?}", expr, expr2);

                // Visit the next block, or the entire nested loop anchored by it.
                if bb == loop_anchor {
                    self.visit_basic_block(bb, iteration_count); // join or widen
                } else if self.loop_anchors.contains(&bb) {
                    last_block = self.compute_fixed_point(bb);
                } else {
                    self.visit_basic_block(bb, 0); // conditional expressions
                }

                // Check for a fixed point, once two iterations with widened variables were executed.
                if iteration_count > 3
                    && !self.out_state[&last_block].subset(&old_state[&last_block])
                    && self.contin
                {
                    // There is some path for which self.bv.current_environment.value_at(path) includes
                    // a value this is not present in self.out_state[last_block].value_at(path), so any block
                    // that used self.out_state[bb] as part of its input state now needs to get reanalyzed.
                    changed = true;
                    //println!("!!!yes, it changed");
                }
            }
        }
        (changed, last_block)
    }

    /// Join the exit states from all predecessors blocks to get the entry state fo this block.
    /// If a predecessor has not yet been analyzed, its state does not form part of the join.
    /// If no predecessors have been analyzed, the entry state is a default entry state with an
    /// entry condition of TOP.
    /// Note that iteration_count should be 0 except if bb is a loop anchor, in which case it
    /// is greater than 0.
    #[logfn_inputs(TRACE)]
    fn get_initial_state_from_predecessors(
        &mut self,
        bb: mir::BasicBlock,
        iteration_count: usize,
    ) -> Environment {
        let mut predecessor_states_and_conditions: Vec<(Environment, Rc<AbstractValue>)> =
            self.bv.mir.predecessors()[bb]
                .iter()
                .filter_map(|pred_bb| {
                    let is_loop_back = self.dominators.is_dominated_by(*pred_bb, bb);
                    if iteration_count == 1 && is_loop_back {
                        // For the first iteration of the loop body we only want state that
                        // precedes the body. Normally, the loop body's state will be in the
                        // default state and thus get ignored, but if the loop is nested there
                        // will be state from the previous iteration of the outer loop.
                        return None;
                    }
                    if iteration_count > 1 && !is_loop_back {
                        // Once the loop body has been interpreted in its initial state (iteration 1)
                        // we only want state from the looping back branches.
                        return None;
                    }
                    let pred_state = &self.out_state[pred_bb];
                    if let Some(pred_exit_condition) = pred_state.exit_conditions.get(&bb) {
                        if pred_exit_condition.as_bool_if_known().unwrap_or(true) {
                            trace!(
                                "pred {:?} exits on condition {:?} with {:?}",
                                pred_bb,
                                pred_exit_condition,
                                pred_state
                            );
                            Some((pred_state.clone(), pred_exit_condition.clone()))
                        } else {
                            // If pred_bb is known to have a false exit condition for bb it can be ignored.
                            None
                        }
                    } else {
                        // If pred_state does not have an exit condition map, it is in its default state
                        // which means it has not yet been visited, or it is code that is known to always
                        // panic at runtime. Either way, we don't want to include its out state here.
                        None
                    }
                })
                .collect();
        if predecessor_states_and_conditions.is_empty() {
            // bb is unreachable, at least in this iteration.
            // We therefore give it a false entry condition so that the block analyses knows
            // the block is unreachable.
            let mut initial_state = self.bv.first_environment.clone();
            initial_state.entry_condition = Rc::new(abstract_value::FALSE);
            return initial_state;
        }
        if predecessor_states_and_conditions.len() == 1 {
            let (mut state, entry_condition) = predecessor_states_and_conditions.remove(0);
            state.entry_condition = entry_condition;
            state.exit_conditions = HashTrieMap::default();
            state
        } else {
            let entry_condition = predecessor_states_and_conditions
                .iter()
                .map(|(_, c)| c.clone())
                .fold1(|c1, c2| c1.or(c2))
                .unwrap();
            trace!("entry_condition {:?}", entry_condition);
            let mut state = predecessor_states_and_conditions
                .into_iter()
                .fold1(|(state1, cond1), (state2, cond2)| {
                    (state2.conditional_join(state1, &cond2, &cond1), cond1)
                })
                .expect("one or more states to fold into something")
                .0;
            state.entry_condition = entry_condition;
            state
        }
    }
}

/// Do a topological sort, breaking loops by preferring lower block indices, using dominance
/// to determine if there is a loop (if a is predecessor of b and b dominates a then they
/// form a loop and we'll emit the one with the lower index first).
#[logfn_inputs(TRACE)]
fn add_predecessors_then_root_block<'tcx>(
    mir: &'tcx mir::Body<'tcx>,
    root_block: mir::BasicBlock,
    dominators: &Dominators<mir::BasicBlock>,
    loop_anchors: &mut HashSet<mir::BasicBlock>,
    block_indices: &mut Vec<mir::BasicBlock>,
    already_added: &mut HashSet<mir::BasicBlock>,
) {
    if !already_added.insert(root_block) {
        return;
    }
    for pred_bb in mir.predecessors()[root_block].iter() {
        if already_added.contains(pred_bb) {
            continue;
        };
        if dominators.is_dominated_by(*pred_bb, root_block) {
            // pred_bb has still to be added, so it has a greater index than root_block, making root_block the loop anchor.
            checked_assume!(root_block.index() < pred_bb.index());
            // Root block has a smaller index than pred_bb because it has not already been added.
            loop_anchors.insert(root_block);
            continue;
        }
        add_predecessors_then_root_block(
            mir,
            *pred_bb,
            dominators,
            loop_anchors,
            block_indices,
            already_added,
        );
    }
    assume!(block_indices.len() < std::usize::MAX); // We'll run out of memory long  before this overflows
    block_indices.push(root_block);
}

// Perform a topological sort on the basic blocks so that blocks are analyzed after their
// predecessors (except in the case of loop anchors).
#[logfn_inputs(TRACE)]
#[logfn(TRACE)]
fn get_sorted_block_indices(
    mir: &'_ mir::Body<'_>,
    dominators: &Dominators<mir::BasicBlock>,
) -> (Vec<mir::BasicBlock>, HashSet<mir::BasicBlock>) {
    let mut block_indices = Vec::new();
    let mut already_added = HashSet::new();
    let mut loop_anchors = HashSet::new();
    for bb in mir.basic_blocks().indices() {
        add_predecessors_then_root_block(
            mir,
            bb,
            &dominators,
            &mut loop_anchors,
            &mut block_indices,
            &mut already_added,
        );
    }
    (block_indices, loop_anchors)
}
