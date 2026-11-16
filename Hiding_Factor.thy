theory Hiding_Factor
  imports "Axiomatic_CyPhyCircus.Ax_CyPhyCircus"
begin

section \<open>Hiding factorisation\<close>

text \<open>The laws that take a hiding past an operator, in the form in which the hiding moves outward: HI-07 past a
  sequence, RN-05 past a renaming, HI-08 with HI-03 past a parallel composition, HI-06 for a union. The method
  cyphy_factor_hiding of tactics.thy applies them.\<close>

lemma hide_seq_factor:
  fixes cont pre :: "'e cyphyprocess"
  shows "cHide cont H = cont \<Longrightarrow> cSeq (cHide pre H) cont = cHide (cSeq pre cont) H"
  by (simp add: ax_hide_seq_unit)

lemma hide_rename_empty_factor:
  fixes pr :: "'e cyphyprocess"
  shows "cRename ({} :: 'e \<leftrightarrow> 'e) (cHide pr H) = cHide (cRename ({} :: 'e \<leftrightarrow> 'e) pr) H"
  by (rule ax_rename_hide) simp_all

lemma hide_par_skip_factor:
  fixes A :: "'e cyphyprocess"
  shows "S \<inter> H = {} \<Longrightarrow>
    cParallelAct 0\<^sub>L 0\<^sub>L S (cHide A H) cSkip = cHide (cParallelAct 0\<^sub>L 0\<^sub>L S A cSkip) H"
  by (subst ax_hide_parallelAct_unit) (simp_all add: ax_hide_skip)

lemma hide_par_factor:
  fixes pr mem :: "'e cyphyprocess"
  shows "cHide mem H = mem \<Longrightarrow> S \<inter> H = {} \<Longrightarrow>
    cParallelAct 0\<^sub>L 0\<^sub>L S (cHide pr H) mem = cHide (cParallelAct 0\<^sub>L 0\<^sub>L S pr mem) H"
  by (simp add: ax_hide_parallelAct_unit)

lemma hide_par_factor_right:
  fixes pr mem :: "'e cyphyprocess"
  shows "cHide mem H = mem \<Longrightarrow> S \<inter> H = {} \<Longrightarrow>
    cParallelAct 0\<^sub>L 0\<^sub>L S mem (cHide pr H) = cHide (cParallelAct 0\<^sub>L 0\<^sub>L S mem pr) H"
  by (simp add: ax_hide_parallelAct_unit)

lemma hide_event_skip_id:
  "e \<notin> H \<Longrightarrow> cHide (cEventPrefix e cSkip) H = (cEventPrefix e cSkip :: 'e cyphyprocess)"
  by (simp add: cHide_event_visible ax_hide_skip)

lemma hide_par_unchanged:
  fixes A B :: "'e cyphyprocess"
  shows "cHide A H = A \<Longrightarrow> cHide B H = B \<Longrightarrow> S \<inter> H = {} \<Longrightarrow>
    cHide (cParallelAct 0\<^sub>L 0\<^sub>L S A B) H = cParallelAct 0\<^sub>L 0\<^sub>L S A B"
  by (simp add: ax_hide_parallelAct_unit)

subsection \<open>The hiding of a union, one of the two sets past the operator\<close>

lemma hide_seq_factor_Un1:
  fixes P Q :: "'e cyphyprocess"
  shows "cHide Q A = Q \<Longrightarrow> cSeq (cHide P (A \<union> B)) Q = cHide (cSeq (cHide P B) Q) A"
  by (simp only: ax_hide_twice[symmetric, of P B A] Un_commute[of A B] hide_seq_factor)

lemma hide_seq_factor_Un2:
  fixes P Q :: "'e cyphyprocess"
  shows "cHide Q B = Q \<Longrightarrow> cSeq (cHide P (A \<union> B)) Q = cHide (cSeq (cHide P A) Q) B"
  by (simp only: ax_hide_twice[symmetric, of P A B] hide_seq_factor)

lemma hide_par_factor_Un1:
  fixes P Q :: "'e cyphyprocess"
  shows "cHide Q A = Q \<Longrightarrow> S \<inter> A = {} \<Longrightarrow>
    cParallelAct 0\<^sub>L 0\<^sub>L S (cHide P (A \<union> B)) Q = cHide (cParallelAct 0\<^sub>L 0\<^sub>L S (cHide P B) Q) A"
  by (simp only: ax_hide_twice[symmetric, of P B A] Un_commute[of A B] hide_par_factor)

lemma hide_par_factor_Un2:
  fixes P Q :: "'e cyphyprocess"
  shows "cHide Q B = Q \<Longrightarrow> S \<inter> B = {} \<Longrightarrow>
    cParallelAct 0\<^sub>L 0\<^sub>L S (cHide P (A \<union> B)) Q = cHide (cParallelAct 0\<^sub>L 0\<^sub>L S (cHide P A) Q) B"
  by (simp only: ax_hide_twice[symmetric, of P A B] hide_par_factor)

subsection \<open>Prefixes as event prefixes and prefix choices\<close>

lemma cSync_event_prefix_fun: "cSyncPrefix c = cEventPrefix (evsimple c)"
  by (rule ext) (rule ax_cSync_event_prefix)

lemma cInputPrefix_mprefix_UNIV:
  "inj (prism_build c) \<Longrightarrow>
    cInputPrefix c UNIV (\<lambda>x. (\<lambda>_. True, P x)) =
      cPrefixChoice (range (prism_build c)) (\<lambda>e. P (inv (prism_build c) e) :: 'e cyphyprocess)"
  by (simp add: cInputPrefix_mprefix)

subsection \<open>The share loop interrupted by one event\<close>

(* From IN-01, HI-01 and HI-03. *)

definition wait_step :: "'e \<Rightarrow> 'e \<Rightarrow> 'e cyphyprocess \<Rightarrow> 'e cyphyprocess" where
"wait_step t s X = cExtChoice (cEventPrefix t cSkip) (cEventPrefix s X)"

lemma mono_prefix: "mono (\<lambda>X :: 'e cyphyprocess. cEventPrefix s X)"
  by (rule monoI) (simp add: cEventPrefix_mono)

lemma wait_step_mono: "mono (wait_step t s)"
  by (rule monoI) (simp add: wait_step_def cExtChoice_mono cEventPrefix_mono)

lemma cInterrupt_event:
  "cInterrupt (cEventPrefix e P) Q = cExtChoice Q (cEventPrefix e (cInterrupt P (Q :: 'e cyphyprocess)))"
  using ax_interrupt_mprefix[of "{e}" "\<lambda>_. P" Q] by (simp only: cPrefixChoice_singleton)

lemma wait_commute:
  "cInterrupt (cEventPrefix s X) (cEventPrefix t cSkip) = wait_step t s (cInterrupt X (cEventPrefix t cSkip))"
  unfolding wait_step_def by (simp only: cInterrupt_event)

lemma wait_step_unfold: "lfp (wait_step t s) = wait_step t s (lfp (wait_step t s))"
  by (rule lfp_unfold[OF wait_step_mono])

lemma interrupt_iterate:
  "cInterrupt (((\<lambda>X. cEventPrefix s X) ^^ n) Z) (cEventPrefix t cSkip) =
     (wait_step t s ^^ n) (cInterrupt (Z :: 'e cyphyprocess) (cEventPrefix t cSkip))"
  by (induct n) (simp_all add: wait_commute)

lemma wait_step_hide_commute:
  assumes "t \<notin> H" "s \<notin> H" "t \<noteq> s"
  shows "cHide (wait_step t s X) H = wait_step t s (cHide X H)"
  unfolding wait_step_def
  apply (simp only: cEventPrefix_choice)
  apply (subst ax_hide_mprefix_disjoint)
   apply (simp add: assms)
  apply (rule cPrefixChoice_cong_simp)
   apply (rule refl)
  apply (elim insertE emptyE)
   apply (simp add: assms ax_hide_skip)
  apply (simp add: assms assms(3)[symmetric])
  done

lemma hide_wait_iterate:
  assumes "cHide Z H = Z" "t \<notin> H" "s \<notin> H" "t \<noteq> s"
  shows "cHide ((wait_step t s ^^ n) Z) H = (wait_step t s ^^ n) (Z :: 'e cyphyprocess)"
  by (induct n) (simp_all add: assms wait_step_hide_commute)

lemma hide_lfp_wait_step:
  assumes "t \<notin> H" "s \<notin> H" "t \<noteq> s"
  shows "cHide (lfp (wait_step t s)) H = wait_step t s (cHide (lfp (wait_step t s)) H)"
proof -
  have "cHide (lfp (wait_step t s)) H = cHide (wait_step t s (lfp (wait_step t s))) H"
    by (simp only: wait_step_unfold[symmetric])
  also have "... = wait_step t s (cHide (lfp (wait_step t s)) H)" by (rule wait_step_hide_commute[OF assms])
  finally show ?thesis .
qed

end
