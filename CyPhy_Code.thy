section \<open> Executable Syntax for Axiomatic CyPhyCircus \<close>

theory CyPhy_Code
  imports Ax_CyPhyCircus
begin

text \<open>
  This theory provides an executable syntax for the opaque
  @{typ "('e, 's) cyphyaction"} type.
\<close>

subsection \<open> Process Syntax \<close>

datatype 'e cyphy_code =
    CodeStop
  | CodeSkip
  | CodePrefix 'e "'e cyphy_code"
  | CodeExtChoice "'e cyphy_code" "'e cyphy_code"
  | CodeIntChoice "'e cyphy_code" "'e cyphy_code"
  | CodeSeq "'e cyphy_code" "'e cyphy_code"
  | CodeVar nat
  | CodeMu "'e cyphy_code"

subsection \<open> Denotation into the Axiomatic Carrier \<close>


fun ax_denote :: "('e, 's) cyphyaction list \<Rightarrow> 'e cyphy_code \<Rightarrow> ('e, 's) cyphyaction" where
  "ax_denote env CodeStop = cStop"
| "ax_denote env CodeSkip = cSkip"
| "ax_denote env (CodePrefix e P) = cEventPrefix e (ax_denote env P)"
| "ax_denote env (CodeExtChoice P Q) = cExtChoice (ax_denote env P) (ax_denote env Q)"
| "ax_denote env (CodeIntChoice P Q) = sup (ax_denote env P) (ax_denote env Q)"
| "ax_denote env (CodeSeq P Q) = cSeq (ax_denote env P) (ax_denote env Q)"
| "ax_denote env (CodeVar n) = (if n < length env then env ! n else cStop)"
| "ax_denote env (CodeMu P) = gfp (\<lambda> X. ax_denote (X # env) P)"


lemma ax_denote_mono:
  "list_all2 (\<le>) env\<^sub>1 env\<^sub>2 \<Longrightarrow> ax_denote env\<^sub>1 P \<le> ax_denote env\<^sub>2 P"
proof (induction P arbitrary: env\<^sub>1 env\<^sub>2)
  case (CodePrefix e P)
  then show ?case by (simp add: cEventPrefix_mono)
next
  case (CodeExtChoice P Q)
  then show ?case by (simp add: cExtChoice_mono)
next
  case (CodeIntChoice P Q)
  then show ?case by (metis ax_denote.simps(5) sup_mono)
next
  case (CodeSeq P Q)
  then show ?case by (simp add: cSeq_mono)
next
  case (CodeVar n)
  then show ?case
    by (cases "n < length env\<^sub>1") (auto simp add: list_all2_conv_all_nth)
next
  case (CodeMu P)
  then show ?case
    by (auto intro!: gfp_mono CodeMu.IH simp add: list_all2_conv_all_nth nth_Cons')
qed simp_all

lemma ax_denote_body_mono: "mono (\<lambda> X. ax_denote (X # env) P)"
  by (rule monoI, rule ax_denote_mono, simp add: list_all2_refl)

lemma ax_denote_mu_unfold:
  "ax_denote env (CodeMu P) = ax_denote (ax_denote env (CodeMu P) # env) P"
proof -
  have "gfp (\<lambda> X. ax_denote (X # env) P)
        = ax_denote (gfp (\<lambda> X. ax_denote (X # env) P) # env) P"
    using ax_denote_body_mono gfp_unfold by blast
  thus ?thesis by simp
qed

subsection \<open> Lifting and Substitution \<close>

text \<open>
   \<open>code_shift k P\<close> increments variables
  \<open>\<ge> k\<close>, and \<open>code_subst k S P\<close> replaces variable \<open>k\<close> by \<open>S\<close> (renumbering
  the variables above it).  \<open>code_unfold_mu P\<close> performs one
  unfolding of @{term "CodeMu P"}; it is the executable counterpart of
  @{thm [source] ax_denote_mu_unfold}.
\<close>

fun code_shift :: "nat \<Rightarrow> 'e cyphy_code \<Rightarrow> 'e cyphy_code" where
  "code_shift k CodeStop = CodeStop"
| "code_shift k CodeSkip = CodeSkip"
| "code_shift k (CodePrefix e P) = CodePrefix e (code_shift k P)"
| "code_shift k (CodeExtChoice P Q) = CodeExtChoice (code_shift k P) (code_shift k Q)"
| "code_shift k (CodeIntChoice P Q) = CodeIntChoice (code_shift k P) (code_shift k Q)"
| "code_shift k (CodeSeq P Q) = CodeSeq (code_shift k P) (code_shift k Q)"
| "code_shift k (CodeVar n) = CodeVar (if n < k then n else Suc n)"
| "code_shift k (CodeMu P) = CodeMu (code_shift (Suc k) P)"

fun code_subst :: "nat \<Rightarrow> 'e cyphy_code \<Rightarrow> 'e cyphy_code \<Rightarrow> 'e cyphy_code" where
  "code_subst k S CodeStop = CodeStop"
| "code_subst k S CodeSkip = CodeSkip"
| "code_subst k S (CodePrefix e P) = CodePrefix e (code_subst k S P)"
| "code_subst k S (CodeExtChoice P Q) = CodeExtChoice (code_subst k S P) (code_subst k S Q)"
| "code_subst k S (CodeIntChoice P Q) = CodeIntChoice (code_subst k S P) (code_subst k S Q)"
| "code_subst k S (CodeSeq P Q) = CodeSeq (code_subst k S P) (code_subst k S Q)"
| "code_subst k S (CodeVar n) =
     (if n = k then S else if k < n then CodeVar (n - 1) else CodeVar n)"
| "code_subst k S (CodeMu P) = CodeMu (code_subst (Suc k) (code_shift 0 S) P)"

abbreviation code_unfold_mu :: "'e cyphy_code \<Rightarrow> 'e cyphy_code" where
  "code_unfold_mu P \<equiv> code_subst 0 (CodeMu P) P"

subsection \<open> Loop-Depth-Bounded Trace Checker \<close>

text \<open>
  \<open>loopDepth\<close> argument bounds the number of \<open>CodeMu\<close> unfoldings performed.
\<close>

datatype acceptance = Accepted | Rejected | UnknownCutoff

fun bounded_or :: "bool option \<Rightarrow> bool option \<Rightarrow> bool option" where
  "bounded_or (Some True) q = Some True"
| "bounded_or p (Some True) = Some True"
| "bounded_or (Some False) (Some False) = Some False"
| "bounded_or p q = None"

fun bounded_and :: "bool option \<Rightarrow> bool option \<Rightarrow> bool option" where
  "bounded_and (Some False) q = Some False"
| "bounded_and p (Some False) = Some False"
| "bounded_and (Some True) (Some True) = Some True"
| "bounded_and p q = None"

fun code_terminates :: "nat \<Rightarrow> 'e cyphy_code \<Rightarrow> bool option" where
  "code_terminates loopDepth CodeStop = Some False"
| "code_terminates loopDepth CodeSkip = Some True"
| "code_terminates loopDepth (CodePrefix e P) = Some False"
| "code_terminates loopDepth (CodeExtChoice P Q) =
     bounded_or (code_terminates loopDepth P) (code_terminates loopDepth Q)"
| "code_terminates loopDepth (CodeIntChoice P Q) =
     bounded_or (code_terminates loopDepth P) (code_terminates loopDepth Q)"
| "code_terminates loopDepth (CodeSeq P Q) =
     bounded_and (code_terminates loopDepth P) (code_terminates loopDepth Q)"
| "code_terminates loopDepth (CodeVar n) = Some False"
| "code_terminates 0 (CodeMu P) = None"
| "code_terminates (Suc loopDepth) (CodeMu P) =
     code_terminates loopDepth (code_unfold_mu P)"

fun code_after ::
  "nat \<Rightarrow> 'e \<Rightarrow> 'e cyphy_code \<Rightarrow> 'e cyphy_code list \<times> bool"
where
  "code_after loopDepth e CodeStop = ([], False)"
| "code_after loopDepth e CodeSkip = ([], False)"
| "code_after loopDepth e (CodePrefix f P) =
     (if f = e then ([P], False) else ([], False))"
| "code_after loopDepth e (CodeExtChoice P Q) =
     (let (Ps, cutP) = code_after loopDepth e P;
          (Qs, cutQ) = code_after loopDepth e Q
      in (Ps @ Qs, cutP \<or> cutQ))"
| "code_after loopDepth e (CodeIntChoice P Q) =
     (let (Ps, cutP) = code_after loopDepth e P;
          (Qs, cutQ) = code_after loopDepth e Q
      in (Ps @ Qs, cutP \<or> cutQ))"
| "code_after loopDepth e (CodeSeq P Q) =
     (let (Ps, cutP) = code_after loopDepth e P;
          left = map (\<lambda> P'. CodeSeq P' Q) Ps
      in case code_terminates loopDepth P of
           Some True \<Rightarrow>
             (let (Qs, cutQ) = code_after loopDepth e Q
              in (left @ Qs, cutP \<or> cutQ))
         | Some False \<Rightarrow> (left, cutP)
         | None \<Rightarrow> (left, True))"
| "code_after loopDepth e (CodeVar n) = ([], False)"
| "code_after 0 e (CodeMu P) = ([], True)"
| "code_after (Suc loopDepth) e (CodeMu P) =
     code_after loopDepth e (code_unfold_mu P)"

definition combine_acceptance :: "bool \<Rightarrow> acceptance list \<Rightarrow> acceptance" where
  "combine_acceptance cutoff results =
     (if Accepted \<in> set results then Accepted
      else if cutoff \<or> UnknownCutoff \<in> set results then UnknownCutoff
      else Rejected)"

fun code_accepts ::
  "nat \<Rightarrow> 'e cyphy_code \<Rightarrow> 'e list \<Rightarrow> acceptance"
where
  "code_accepts loopDepth P [] = Accepted"
| "code_accepts loopDepth P (e # t) =
     (let (Ps, cutoff) = code_after loopDepth e P
      in combine_acceptance cutoff (map (\<lambda> P'. code_accepts loopDepth P' t) Ps))"

text \<open>
  The property below is pointwise in the trace.  Quickcheck quantifies its free
  trace variable and searches for a trace within \<open>traceDepth\<close> that is accepted
  by the implementation but definitely rejected by the specification.  A
  specification result of \<open>UnknownCutoff\<close> cannot therefore be reported as a
  violation.
\<close>

definition bounded_trace_inclusion ::
  "nat \<Rightarrow> nat \<Rightarrow> 'e cyphy_code \<Rightarrow> 'e cyphy_code \<Rightarrow> 'e list \<Rightarrow> bool"
where
  "bounded_trace_inclusion loopDepth traceDepth spec impl t \<longleftrightarrow>
    (length t \<le> traceDepth \<and>
       code_accepts loopDepth impl t = Accepted
     \<longrightarrow> code_accepts loopDepth spec t \<noteq> Rejected)"


text \<open>
  Bridge lemmas from the channel/prism layer to concrete events, used when
  relating surface models to their executable descriptions: a channel
  instantiated with @{const chinst1} synchronises on the event built from
  the underlying channel and the fixed value.
\<close>

lemma evsimple_chinst1:
  "evsimple (chinst1 c v) = build\<^bsub>c\<^esub> v"
  by (simp add: evsimple_def chinst1_def)

lemma ax_cSync_chinst1_event_prefix:
  "cSyncPrefix (chinst1 c v) P = cEventPrefix (build\<^bsub>c\<^esub> v) P"
  by (simp add: ax_cSync_event_prefix evsimple_chinst1)

end
