theory tactics
  imports Axiomatic_CyPhyCircus.Ax_CyPhyCircus Codegen Hiding_Fusion "HOL-Eisbach.Eisbach"
begin

section \<open>Shared refinement and normalisation methods\<close>

named_theorems rct_defs (* define a theorem set for process definitions so unfolding can be done easier *)

lemmas rct_unfolding = ax_cSync_chinst1_event_prefix evsimple_chinst1
  ctor_prism_def chinst1_def evsimple_def refinement_prism_build
  ref_by_cyphyaction_def order_refl

method rct_refine_core =
  (simp only: rct_defs ax_step_laws chan_defs rct_unfolding)

method rct_channel_sets =
  ((subst csbasic_csbasic2_eq csinsert_cs_insert2_eq;
    (match conclusion in "wb_prism c" for c \<Rightarrow> \<open>solves \<open>simp\<close>\<close> \<bar> _ \<Rightarrow> \<open>succeed\<close>))+)?

lemma rnsingle_enum:
  "rnsingle c\<^sub>1 c\<^sub>2 = (\<lambda>v. (build\<^bsub>c\<^sub>1\<^esub> v, build\<^bsub>c\<^sub>2\<^esub> v)) ` set enum_class.enum"
  unfolding rnsingle_def by (auto simp add: enum_UNIV)

lemma rncollect_enum:
  "rncollect c\<^sub>1 c\<^sub>2 UNIV f =
     (\<lambda>x. (build\<^bsub>c\<^sub>1\<^esub> (fst (fst (f x))), build\<^bsub>c\<^sub>2\<^esub> (snd (fst (f x))))) `
       set (filter (\<lambda>x. snd (f x)) enum_class.enum)"
  unfolding rncollect_def by (auto simp add: enum_UNIV)

method rct_renamings =
  ((simp only: rninsert_def rnsingle_enum rncollect_enum)?)

method rct_normalise =
  ((simp only: rct_defs ax_executable_step_laws cyphy_normalisation
      ax_cSync_chinst1_event_prefix evsimple_chinst1 interrupt_sync_loop_is_lfp
      ref_by_cyphyaction_def order_refl),
   rct_channel_sets, rct_renamings)

named_theorems cyphy_hiding_outward
  \<open>proved outward hiding equations with their side conditions\<close>

lemmas [cyphy_hiding_outward] = cHide_factor_event cHide_factor_visible_event
  cHide_factor_mprefix cHide_factor_internal_choice
  cHide_factor_indexed_internal_choice cHide_factor_seq
  cHide_factor_parallelAct_unit ax_hide_twice

method cyphy_mono =
  (rule monoI,
   simp add: le_fun_def less_eq_prod_def case_prod_unfold mono_rule)

text \<open>cyphy_factor_hiding moves the hidings of a process outward: cyphy_hide_out takes one step, and
  cyphy_hide_side proves the conditions of the law of that step.\<close>

lemmas cyphy_channel_unfolding = csinsert_def csbasic_def chan_defs ctor_prism_def refinement_prism_build
  evsimple_def chinst1_def chinstn_def

method cyphy_hide_rec_step =
  ((simp only: SEXP_def)?,
   ((subst cInputPrefix_mprefix_UNIV, solves \<open>simp add: inj_def cyphy_channel_unfolding\<close>)+)?,
   hide_prefix_choice forms: SEXP_def ax_cSync_event_prefix evsimple_chinst1 ax_cOutput_event_prefix
     disjoint: cyphy_channel_unfolding hidden: cyphy_channel_unfolding inv_f_f inj_def)

method cyphy_hide_side =
  (solves \<open>match conclusion in
     "cHide cSkip H = cSkip" for H \<Rightarrow> \<open>rule ax_hide_skip\<close>
   \<bar> "cHide (cParallelAct 0\<^sub>L 0\<^sub>L S A B) H = cParallelAct 0\<^sub>L 0\<^sub>L S A B" for S A B H \<Rightarrow>
       \<open>rule hide_par_unchanged, cyphy_hide_side, cyphy_hide_side, cyphy_hide_side\<close>
   \<bar> "cHide (lfp F v) H = lfp F v" for F v H \<Rightarrow>
       \<open>rule hide_lfp_fun, cyphy_mono, cyphy_hide_rec_step\<close>
   \<bar> "cHide (cInterrupt P Q) H = cInterrupt P Q" for P Q H \<Rightarrow>
       \<open>(simp only: ax_cSync_event_prefix cSync_event_prefix_fun)?, rule wait_interrupt_hide,
         cyphy_hide_side, cyphy_hide_side, cyphy_hide_side\<close>
   \<bar> "cHide P H = P" for P H \<Rightarrow>
       \<open>(simp only: ax_cSync_event_prefix)?, rule hide_event_skip_id, cyphy_hide_side\<close>
   \<bar> "A \<inter> B = {}" for A B \<Rightarrow>
       \<open>auto simp add: cyphy_channel_unfolding rncollect_def rnsingle_def rninsert_def\<close>
   \<bar> "single_valued R" for R \<Rightarrow>
       \<open>auto simp add: cyphy_channel_unfolding rncollect_def rnsingle_def rninsert_def single_valued_def\<close>
   \<bar> "x \<notin> A" for x A \<Rightarrow> \<open>auto simp add: cyphy_channel_unfolding\<close>
   \<bar> "x \<noteq> y" for x y \<Rightarrow> \<open>auto simp add: cyphy_channel_unfolding\<close>\<close>)

method cyphy_hide_out =
  ( (subst ax_hide_empty)
  | (subst ax_rename_hide, cyphy_hide_side, cyphy_hide_side, cyphy_hide_side)
  | (subst hide_par_factor, cyphy_hide_side, cyphy_hide_side)
  | (subst hide_par_factor_right, cyphy_hide_side, cyphy_hide_side)
  | (subst hide_seq_factor, cyphy_hide_side)
  | (subst ax_hide_twice)
  | (subst hide_seq_factor_Un1, cyphy_hide_side)
  | (subst hide_seq_factor_Un2, cyphy_hide_side)
  | (subst hide_par_factor_Un1, cyphy_hide_side, cyphy_hide_side)
  | (subst hide_par_factor_Un2, cyphy_hide_side, cyphy_hide_side))

method cyphy_factor_hiding uses add =
  ((simp only: cyphy_hiding_outward HOL.simp_thms add)?, (cyphy_hide_out+)?)

text \<open>rct_refine unfolds the definitions declared rct_defs and applies cyphy_factor_hiding. It then
  tries rct_refine_core, then the monotonicity laws, then rct_normalise.
  The first two are kept only if they prove the goal.\<close>
method rct_refine =
  (((simp only: rct_defs)?, cyphy_factor_hiding),
  (solves \<open>rct_refine_core\<close> |
   solves \<open>auto intro!: cyphy_refinement intro: cyphy_joint_lfp_mono cyphy_joint_gfp_mono
     simp add: rct_defs ax_executable_step_laws cyphy_normalisation
       ref_by_cyphyaction_def\<close> | rct_normalise))

end
