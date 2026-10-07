theory tactics
  imports Ax_CyPhyCircus "HOL-Eisbach.Eisbach"
begin

section \<open>Shared refinement and normalisation methods\<close>

named_theorems rct_defs (* define a theorem set for process definitions so unfolding can be done easier *)

lemmas rct_unfolding = ax_cSync_chinst1_event_prefix evsimple_chinst1
  ctor_prism_def chinst1_def evsimple_def refinement_prism_build
  ref_by_cyphyaction_def order_refl

method rct_refine_core =
  (simp only: rct_defs ax_step_laws chan_defs rct_unfolding)

method rct_normalise =
  (simp only: rct_defs ax_executable_step_laws cyphy_normalisation
     chan_defs rct_unfolding)

text \<open>rct_refine tries rct_refine_core, then the monotonicity laws, then rct_normalise.
  The first two are kept only if they prove the goal.\<close>
method rct_refine =
  (solves \<open>rct_refine_core\<close> |
   solves \<open>auto intro!: cyphy_refinement
     simp add: rct_defs ax_executable_step_laws cyphy_normalisation
       ref_by_cyphyaction_def\<close> | rct_normalise)

end
