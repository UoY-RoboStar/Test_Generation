theory Fixed_Point_Fusion
  imports Main
begin

section \<open>Fixed-point fusion\<close>

text \<open>G (lfp F) = lfp F' when G commutes with the step functions (G o F = F' o G), is strict and distributes
  over nonempty suprema. UTP is Hoare and He, Unifying Theories of Programming (1998).\<close>

(* UTP Exercise 2.6.4(2); law 2.6 L1 *)
lemma lfp_fusion_ge:
  fixes F :: "'a::complete_lattice \<Rightarrow> 'a" and F' :: "'b::complete_lattice \<Rightarrow> 'b" and G :: "'a \<Rightarrow> 'b"
  assumes monoF: "mono F" and comm: "\<And>X. G (F X) = F' (G X)"
  shows "lfp F' \<le> G (lfp F)"
proof (rule lfp_lowerbound)
  have "F' (G (lfp F)) = G (F (lfp F))" by (simp add: comm)
  also have "... = G (lfp F)" by (subst lfp_unfold[OF monoF, symmetric]) (rule refl)
  finally show "F' (G (lfp F)) \<le> G (lfp F)" by simp
qed

(* UTP p. 102, Theorem 4.2.12(1) *)
lemma lfp_fusion_le:
  fixes F :: "'a::complete_lattice \<Rightarrow> 'a" and F' :: "'b::complete_lattice \<Rightarrow> 'b" and G :: "'a \<Rightarrow> 'b"
  assumes monoF: "mono F" and monoF': "mono F'"
    and comm: "\<And>X. G (F X) \<le> F' (G X)"
    and strict: "G bot \<le> lfp F'"
    and dist: "\<And>M. M \<noteq> {} \<Longrightarrow> G (Sup M) \<le> Sup (G ` M)"
  shows "G (lfp F) \<le> lfp F'"
proof (rule lfp_ordinal_induct[where P = "\<lambda>X. G X \<le> lfp F'" and f = F, OF monoF])
  fix X assume ih: "G X \<le> lfp F'" and "X \<le> lfp F"
  have "G (F X) \<le> F' (G X)" by (rule comm)
  also have "... \<le> F' (lfp F')" by (rule monoD[OF monoF' ih])
  also have "... = lfp F'" by (rule lfp_unfold[OF monoF', symmetric])
  finally show "G (F X) \<le> lfp F'" .
next
  fix M :: "'a set" assume *: "\<forall>X\<in>M. G X \<le> lfp F'"
  show "G (Sup M) \<le> lfp F'"
  proof (cases "M = {}")
    case True then show ?thesis using strict by simp
  next
    case False
    have "G (Sup M) \<le> Sup (G ` M)" by (rule dist[OF False])
    also have "... \<le> lfp F'" using * by (intro Sup_least) auto
    finally show ?thesis .
  qed
qed

(* UTP p. 102, Theorem 4.2.12(2) *)
lemma lfp_fusion:
  fixes F :: "'a::complete_lattice \<Rightarrow> 'a" and F' :: "'b::complete_lattice \<Rightarrow> 'b" and G :: "'a \<Rightarrow> 'b"
  assumes monoF: "mono F" and monoF': "mono F'"
    and comm: "\<And>X. G (F X) = F' (G X)"
    and strict: "G bot = bot"
    and dist: "\<And>M. M \<noteq> {} \<Longrightarrow> G (Sup M) = Sup (G ` M)"
  shows "G (lfp F) = lfp F'"
proof (rule order_antisym)
  show "G (lfp F) \<le> lfp F'"
    by (rule lfp_fusion_le[OF monoF monoF']) (simp_all add: comm strict dist)
  show "lfp F' \<le> G (lfp F)"
    by (rule lfp_fusion_ge[where F = F and F' = F' and G = G]) (rule monoF, rule comm)
qed

end
