theory Small_Navigation_Example
  imports Small_Navigation Small_Navigation_Mutant "Test_Generation.TestGen"
begin

section \<open>Refinement check on the small Navigation example\<close>

text \<open>This theory checks whether the mutant of the small Navigation model refines the original.
  The algorithm states the refinement as ref_by specification implementation and applies
  rct_refine.

  The mutant changes the guard position < target to position <= target.\<close>

declare [[testgen_timeout = 15000]]

text \<open>The definitions that rct_refine unfolds.\<close>

declare
  Small_Navigation.Navigation.Small_Navigation_def [rct_defs]
  Small_Navigation.Navigation.stm_Navigation_small_navigation_def [rct_defs]
  Small_Navigation.Navigation.actionsys_def [rct_defs]
  Small_Navigation_Mutant.Navigation.Small_Navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.stm_Navigation_small_navigation_def [rct_defs]
  Small_Navigation_Mutant.Navigation.actionsys_def [rct_defs]

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
