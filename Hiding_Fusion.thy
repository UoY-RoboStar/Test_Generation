theory Hiding_Fusion
  imports Hiding_Factor Fixed_Point_Fusion "HOL-Eisbach.Eisbach"
begin

section \<open>The share loop through the fixed point\<close>

text \<open>Fixed-point fusion takes the interrupt and the hiding through the share loop: the loop interrupted by a
  process is a recursion (wait_is_lfp, interrupt_loop_is_lfp; IN-01, cInterrupt_bot, UD-04), and the hiding of a
  set without its events leaves that recursion as it is (wait_hide; HI-01, cHide_bot, UD-01).\<close>

lemma wait_is_lfp:
  "cInterrupt (lfp (\<lambda>X. cEventPrefix s X)) (cEventPrefix t cSkip) = lfp (wait_step t s)"
  by (rule lfp_fusion[OF mono_prefix wait_step_mono wait_commute cInterrupt_bot ax_interrupt_Sup])

(* From IN-01 and UD-04. *)
lemma interrupt_loop_is_lfp:
  "cInterrupt (lfp (\<lambda>X. cEventPrefix s X)) Q =
    lfp (\<lambda>X. cExtChoice Q (cEventPrefix s (X :: 'e cyphyprocess)))"
  by (rule lfp_fusion[where G = "\<lambda>P. cInterrupt P Q",
        OF mono_prefix _ cInterrupt_event cInterrupt_bot ax_interrupt_Sup])
     (rule monoI, simp add: cExtChoice_mono cEventPrefix_mono)

lemma interrupt_sync_loop_is_lfp:
  "cInterrupt (lfp (cSyncPrefix c)) Q = lfp (\<lambda>X. cExtChoice Q (cSyncPrefix c (X :: 'e cyphyprocess)))"
  by (simp only: cSync_event_prefix_fun interrupt_loop_is_lfp)

lemma wait_hide:
  assumes "t \<notin> H" "s \<notin> H" "t \<noteq> s"
  shows "cHide (lfp (wait_step t s)) H = lfp (wait_step t s)"
  by (rule lfp_fusion[OF wait_step_mono wait_step_mono wait_step_hide_commute[OF assms] cHide_bot ax_hide_Sup])

lemma wait_interrupt_hide:
  assumes "t \<notin> H" "s \<notin> H" "t \<noteq> s"
  shows "cHide (cInterrupt (lfp (\<lambda>X. cEventPrefix s X)) (cEventPrefix t cSkip)) H =
    cInterrupt (lfp (\<lambda>X. cEventPrefix s X)) (cEventPrefix t (cSkip :: 'e cyphyprocess))"
  by (simp only: wait_is_lfp wait_hide[OF assms])

section \<open>Hiding through a recursion\<close>

(* From UD-01. *)

lemma hide_lfp:
  fixes F :: "'e cyphyprocess \<Rightarrow> 'e cyphyprocess"
  assumes mono: "mono F" and step: "\<And>X. cHide (F X) H = F (cHide X H)"
  shows "cHide (lfp F) H = lfp F"
  by (rule lfp_fusion[OF mono mono step cHide_bot ax_hide_Sup])

lemma hide_lfp_fun:
  fixes F :: "('a \<Rightarrow> 'e cyphyprocess) \<Rightarrow> 'a \<Rightarrow> 'e cyphyprocess"
  assumes mono: "mono F" and step: "\<And>M v. cHide (F M v) H = F (\<lambda>v. cHide (M v) H) v"
  shows "cHide (lfp F v) H = lfp F v"
proof -
  let ?G = "\<lambda>(M :: 'a \<Rightarrow> 'e cyphyprocess) v. cHide (M v) H"
  have "?G (lfp F) = lfp F"
  proof (rule lfp_fusion[OF mono mono])
    show "?G (F M) = F (?G M)" for M
      by (rule ext) (rule step)
    show "?G bot = bot"
      by (simp add: fun_eq_iff cHide_bot)
    show "?G (Sup N) = Sup (?G ` N)" if "N \<noteq> {}" for N
      by (rule ext) (simp add: ax_hide_Sup image_image)
  qed
  then show ?thesis by (rule fun_cong)
qed

section \<open>Methods for one step of a recursion\<close>

(* From HI-01, ALG-03 and HI-03. *)

method hide_prefix_choice uses forms disjoint hidden =
  (simp only: forms cEventPrefix_choice cPrefixChoice_choice_event cEventPrefix_choice_mprefix,
   subst ax_hide_mprefix_disjoint,
   (auto simp add: disjoint)[1],
   rule cPrefixChoice_cong_simp, rule refl,
   (elim insertE emptyE rangeE; simp add: ax_alg_hide_internal ax_hide_skip hidden))

end
