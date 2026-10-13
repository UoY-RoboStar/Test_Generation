theory Small_Navigation_Example
  imports Small_Navigation Small_Navigation_Mutant "Test_Generation.TestGen"
begin

section \<open>Refinement check on the small Navigation example\<close>

text \<open>This theory checks whether the mutant of the small Navigation model refines the original.
  The algorithm states the refinement as ref_by specification implementation and applies
  rct_refine.

  The mutant changes the guard position < target to position <= target.\<close>

declare [[testgen_timeout = 15000]]

text \<open>Definitions of the model that rct_refine unfolds.\<close>

declare
  Small_Navigation.Navigation.Small_Navigation_def [rct_defs]
  Small_Navigation.Navigation.InactiveJct_i0_Navigation_small_navigation_rec_fun_def [rct_defs]
  Small_Navigation.Navigation.Inactive_WaitTarget_Navigation_small_navigation_rec_fun_def [rct_defs]
  Small_Navigation.Navigation.Inactive_WaitForPose_Navigation_small_navigation_rec_fun_def [rct_defs]
  Small_Navigation.Navigation.InactiveJct_CheckPosition_Navigation_small_navigation_rec_fun_def [rct_defs]
  Small_Navigation.Navigation.Inactive_WaitMoveApplied_Navigation_small_navigation_rec_fun_def [rct_defs]
  Small_Navigation.Navigation.Inactive_WaitStopApplied_Navigation_small_navigation_rec_fun_def [rct_defs]
  Small_Navigation.Navigation.InactiveFn_f0_Navigation_small_navigation_rec_fun_def [rct_defs]
  Small_Navigation.Navigation.Trans_Navigation_small_navigation_rec_fun_def [rct_defs]
  Small_Navigation.Navigation.Transc_Navigation_small_navigation_rec_fun_def [rct_defs]
  Small_Navigation.Navigation.Memory_target_Navigation_small_navigation_rec_fun_def [rct_defs]
  Small_Navigation.Navigation.Memory_position_Navigation_small_navigation_rec_fun_def [rct_defs]
  Small_Navigation.Navigation.SSTOP_def [rct_defs]
  Small_Navigation.Navigation.Termination_i0_Navigation_small_navigation_def [rct_defs]
  Small_Navigation.Navigation.Termination_WaitTarget_Navigation_small_navigation_def [rct_defs]
  Small_Navigation.Navigation.During_WaitTarget_Navigation_small_navigation_def [rct_defs]
  Small_Navigation.Navigation.Behaviour_WaitTarget_Navigation_small_navigation_def [rct_defs]
  Small_Navigation.Navigation.Termination_WaitForPose_Navigation_small_navigation_def [rct_defs]
  Small_Navigation.Navigation.During_WaitForPose_Navigation_small_navigation_def [rct_defs]
  Small_Navigation.Navigation.Behaviour_WaitForPose_Navigation_small_navigation_def [rct_defs]
  Small_Navigation.Navigation.Termination_CheckPosition_Navigation_small_navigation_def [rct_defs]
  Small_Navigation.Navigation.Termination_WaitMoveApplied_Navigation_small_navigation_def [rct_defs]
  Small_Navigation.Navigation.During_WaitMoveApplied_Navigation_small_navigation_def [rct_defs]
  Small_Navigation.Navigation.Behaviour_WaitMoveApplied_Navigation_small_navigation_def [rct_defs]
  Small_Navigation.Navigation.Termination_WaitStopApplied_Navigation_small_navigation_def [rct_defs]
  Small_Navigation.Navigation.During_WaitStopApplied_Navigation_small_navigation_def [rct_defs]
  Small_Navigation.Navigation.Behaviour_WaitStopApplied_Navigation_small_navigation_def [rct_defs]
  Small_Navigation.Navigation.Termination_f0_Navigation_small_navigation_def [rct_defs]
  Small_Navigation.Navigation.composeNodes_Navigation_small_navigation_def [rct_defs]
  Small_Navigation.Navigation.ncCoreBehaviour_Navigation_small_navigation_def [rct_defs]
  Small_Navigation.Navigation.ncBehaviour_Navigation_small_navigation_def [rct_defs]
  Small_Navigation.Navigation.machineBody_Navigation_small_navigation_def [rct_defs]
  Small_Navigation.Navigation.varMemory_Navigation_small_navigation_def [rct_defs]
  Small_Navigation.Navigation.stateful_Navigation_small_navigation_def [rct_defs]
  Small_Navigation.Navigation.sharedVarMemory_Navigation_small_navigation_def [rct_defs]
  Small_Navigation.Navigation.stm_Navigation_small_navigation_def [rct_defs]
  Small_Navigation.Navigation.InactiveJct_i0_Navigation_small_navigation_def [rct_defs]
  Small_Navigation.Navigation.Activation_i0_Navigation_small_navigation_def [rct_defs]
  Small_Navigation.Navigation.Active_i0_Navigation_small_navigation_def [rct_defs]
  Small_Navigation.Navigation.Inactive_WaitTarget_Navigation_small_navigation_def [rct_defs]
  Small_Navigation.Navigation.Activation_WaitTarget_Navigation_small_navigation_def [rct_defs]
  Small_Navigation.Navigation.Active_WaitTarget_Navigation_small_navigation_def [rct_defs]
  Small_Navigation.Navigation.Exiting_WaitTarget_Navigation_small_navigation_def [rct_defs]
  Small_Navigation.Navigation.Inactive_WaitForPose_Navigation_small_navigation_def [rct_defs]
  Small_Navigation.Navigation.Activation_WaitForPose_Navigation_small_navigation_def [rct_defs]
  Small_Navigation.Navigation.Active_WaitForPose_Navigation_small_navigation_def [rct_defs]
  Small_Navigation.Navigation.Exiting_WaitForPose_Navigation_small_navigation_def [rct_defs]
  Small_Navigation.Navigation.InactiveJct_CheckPosition_Navigation_small_navigation_def [rct_defs]
  Small_Navigation.Navigation.Activation_CheckPosition_Navigation_small_navigation_def [rct_defs]
  Small_Navigation.Navigation.Active_CheckPosition_Navigation_small_navigation_def [rct_defs]
  Small_Navigation.Navigation.Inactive_WaitMoveApplied_Navigation_small_navigation_def [rct_defs]
  Small_Navigation.Navigation.Activation_WaitMoveApplied_Navigation_small_navigation_def [rct_defs]
  Small_Navigation.Navigation.Active_WaitMoveApplied_Navigation_small_navigation_def [rct_defs]
  Small_Navigation.Navigation.Exiting_WaitMoveApplied_Navigation_small_navigation_def [rct_defs]
  Small_Navigation.Navigation.Inactive_WaitStopApplied_Navigation_small_navigation_def [rct_defs]
  Small_Navigation.Navigation.Activation_WaitStopApplied_Navigation_small_navigation_def [rct_defs]
  Small_Navigation.Navigation.Active_WaitStopApplied_Navigation_small_navigation_def [rct_defs]
  Small_Navigation.Navigation.Exiting_WaitStopApplied_Navigation_small_navigation_def [rct_defs]
  Small_Navigation.Navigation.InactiveFn_f0_Navigation_small_navigation_def [rct_defs]
  Small_Navigation.Navigation.Activation_f0_Navigation_small_navigation_def [rct_defs]
  Small_Navigation.Navigation.Entering_f0_Navigation_small_navigation_def [rct_defs]
  Small_Navigation.Navigation.Active_f0_Navigation_small_navigation_def [rct_defs]
  Small_Navigation.Navigation.Interrupted_f0_Navigation_small_navigation_def [rct_defs]
  Small_Navigation.Navigation.Trans_Navigation_small_navigation_def [rct_defs]
  Small_Navigation.Navigation.Transc_Navigation_small_navigation_def [rct_defs]
  Small_Navigation.Navigation.Memory_target_Navigation_small_navigation_def [rct_defs]
  Small_Navigation.Navigation.Memory_position_Navigation_small_navigation_def [rct_defs]

text \<open>Definitions of the mutant that rct_refine unfolds.\<close>

declare
  Small_Navigation_Mutant.Navigation.Small_Navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.InactiveJct_i0_Navigation_small_navigation_rec_fun_def [rct_defs]
  Small_Navigation_Mutant.Navigation.Inactive_WaitTarget_Navigation_small_navigation_rec_fun_def [rct_defs]
  Small_Navigation_Mutant.Navigation.Inactive_WaitForPose_Navigation_small_navigation_rec_fun_def [rct_defs]
  Small_Navigation_Mutant.Navigation.InactiveJct_CheckPosition_Navigation_small_navigation_rec_fun_def [rct_defs]
  Small_Navigation_Mutant.Navigation.Inactive_WaitMoveApplied_Navigation_small_navigation_rec_fun_def [rct_defs]
  Small_Navigation_Mutant.Navigation.Inactive_WaitStopApplied_Navigation_small_navigation_rec_fun_def [rct_defs]
  Small_Navigation_Mutant.Navigation.InactiveFn_f0_Navigation_small_navigation_rec_fun_def [rct_defs]
  Small_Navigation_Mutant.Navigation.Trans_Navigation_small_navigation_rec_fun_def [rct_defs]
  Small_Navigation_Mutant.Navigation.Transc_Navigation_small_navigation_rec_fun_def [rct_defs]
  Small_Navigation_Mutant.Navigation.Memory_target_Navigation_small_navigation_rec_fun_def [rct_defs]
  Small_Navigation_Mutant.Navigation.Memory_position_Navigation_small_navigation_rec_fun_def [rct_defs]
  Small_Navigation_Mutant.Navigation.SSTOP_def [rct_defs]
  Small_Navigation_Mutant.Navigation.Termination_i0_Navigation_small_navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.Termination_WaitTarget_Navigation_small_navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.During_WaitTarget_Navigation_small_navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.Behaviour_WaitTarget_Navigation_small_navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.Termination_WaitForPose_Navigation_small_navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.During_WaitForPose_Navigation_small_navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.Behaviour_WaitForPose_Navigation_small_navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.Termination_CheckPosition_Navigation_small_navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.Termination_WaitMoveApplied_Navigation_small_navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.During_WaitMoveApplied_Navigation_small_navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.Behaviour_WaitMoveApplied_Navigation_small_navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.Termination_WaitStopApplied_Navigation_small_navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.During_WaitStopApplied_Navigation_small_navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.Behaviour_WaitStopApplied_Navigation_small_navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.Termination_f0_Navigation_small_navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.composeNodes_Navigation_small_navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.ncCoreBehaviour_Navigation_small_navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.ncBehaviour_Navigation_small_navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.machineBody_Navigation_small_navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.varMemory_Navigation_small_navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.stateful_Navigation_small_navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.sharedVarMemory_Navigation_small_navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.stm_Navigation_small_navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.InactiveJct_i0_Navigation_small_navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.Activation_i0_Navigation_small_navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.Active_i0_Navigation_small_navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.Inactive_WaitTarget_Navigation_small_navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.Activation_WaitTarget_Navigation_small_navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.Active_WaitTarget_Navigation_small_navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.Exiting_WaitTarget_Navigation_small_navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.Inactive_WaitForPose_Navigation_small_navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.Activation_WaitForPose_Navigation_small_navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.Active_WaitForPose_Navigation_small_navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.Exiting_WaitForPose_Navigation_small_navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.InactiveJct_CheckPosition_Navigation_small_navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.Activation_CheckPosition_Navigation_small_navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.Active_CheckPosition_Navigation_small_navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.Inactive_WaitMoveApplied_Navigation_small_navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.Activation_WaitMoveApplied_Navigation_small_navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.Active_WaitMoveApplied_Navigation_small_navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.Exiting_WaitMoveApplied_Navigation_small_navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.Inactive_WaitStopApplied_Navigation_small_navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.Activation_WaitStopApplied_Navigation_small_navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.Active_WaitStopApplied_Navigation_small_navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.Exiting_WaitStopApplied_Navigation_small_navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.InactiveFn_f0_Navigation_small_navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.Activation_f0_Navigation_small_navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.Entering_f0_Navigation_small_navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.Active_f0_Navigation_small_navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.Interrupted_f0_Navigation_small_navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.Trans_Navigation_small_navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.Transc_Navigation_small_navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.Memory_target_Navigation_small_navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.Memory_position_Navigation_small_navigation_def [rct_defs]

subsection \<open>Check refinement of model against itself\<close>

text \<open>rct_refine proves that the original model refines itself.\<close>

lemma self_refinement:
  "ref_by Small_Navigation.Navigation.Small_Navigation
    Small_Navigation.Navigation.Small_Navigation"
  by rct_refine

subsection \<open>Refinement of original model against the mutant\<close>

text \<open>rct_refine does not prove this refinement. It leaves one simplified goal of the form
  implementation <= specification.\<close>

lemma
  "ref_by Small_Navigation.Navigation.Small_Navigation
    Small_Navigation_Mutant.Navigation.Small_Navigation"
  apply rct_refine
  oops

subsection \<open>Candidate counterexample\<close>

text \<open>checkRefinement applies rct_refine and passes the two sides of the remaining goal to
  the candidate search.\<close>

ML_val \<open>
  let
    val spec = @{term Small_Navigation.Navigation.Small_Navigation};
    val impl = @{term Small_Navigation_Mutant.Navigation.Small_Navigation};
    val (result, _) = Timeout.apply (Time.fromSeconds 60)
      (fn () => checkRefinement (Named_Target.theory_init \<^theory>) spec impl) ();
  in
    writeln ("original model against the mutant: " ^
      (case result of
        NONE => "refining mutant"
      | SOME NONE => "failed mutant"
      | SOME (SOME _) => "trace generated"))
  end
\<close>

(* TODO (James): the candidate search does not run on this pair. The simplified models
   still contain hiding and interrupt, which the search does not support. *)

(* TODO (James): ref_by is (\<ge>), so internal choice is sup, but Codegen.thy uses inf. *)
end
