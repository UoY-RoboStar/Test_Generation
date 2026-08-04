theory Ax_CyPhyCircus
  imports 
    "CyPhyCircus_Toolkit.CyPhyCircus_Toolkit"
begin

unbundle UTP_Syntax

no_notation disj  (infixr \<open>|\<close> 30)
no_notation funcset (infixr "\<rightarrow>" 60)

subsection \<open> Types and Constants \<close>

typedecl ('e, 's) cyphyaction

type_synonym 'e cyphyprocess = "('e, unit) cyphyaction"

axiomatization where
  action_complete_lattice: "OFCLASS(('e, 's) cyphyaction, complete_lattice_class)"

instantiation cyphyaction :: (type, type) complete_lattice
begin
instance by (fact action_complete_lattice)
end

text \<open>
 \<open>P \<sqsubseteq> Q\<close> means that \<open>Q \<le> P\<close> 
\<close>

instantiation cyphyaction :: (type, type) refine
begin

definition ref_by_cyphyaction ::
  "('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> bool"
where
  "ref_by_cyphyaction = (\<ge>)"

definition sref_by_cyphyaction ::
  "('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> bool"
where
  "sref_by_cyphyaction = (>)"

instance
  apply (intro_classes, unfold_locales)
    apply (metis ref_by_cyphyaction_def sref_by_cyphyaction_def
      inf.order_iff inf.strict_order_iff inf_commute)
   apply (simp add: ref_by_cyphyaction_def)
  apply (simp add: ref_by_cyphyaction_def)
  done

end

subsection \<open> IsaCyPhyCircus Operators \<close>

axiomatization
  cSpec          :: "('a \<Longrightarrow> 's) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('e, 's) cyphyaction" and
  cAssigns       :: "('s \<Rightarrow> 's) \<Rightarrow> ('e, 's) cyphyaction" and
  cSeq           :: "('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction" and
  cCond          :: "('e, 's) cyphyaction \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction" and
  cAlternList    :: "(('s \<Rightarrow> bool) \<times> ('e, 's) cyphyaction) list \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction" and
  cStop          :: "('e, 's) cyphyaction" and
  cChaos         :: "('e, 's) cyphyaction" and
  cGuard         :: "(bool, 's) expr \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction" and
  cAssume        :: "(bool, 's) expr \<Rightarrow> ('e, 's) cyphyaction" and
  cInputPrefix   :: "('a, 'e) channel \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> (('s \<Rightarrow> bool) \<times> ('e, 's) cyphyaction)) \<Rightarrow> ('e, 's) cyphyaction" and
  cOutputPrefix  :: "('a, 'e) channel \<Rightarrow> ('a, 's) expr \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction" and
  cSyncPrefix    :: "(unit, 'e) channel \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction" and
  cEventPrefix   :: "'e \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction" and
  cExtChoice     :: "('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction" and
  cExtChoiceIdx  :: "'i set \<Rightarrow> ('i \<Rightarrow> ('e, 's) cyphyaction) \<Rightarrow> ('e, 's) cyphyaction" and
  cRename        :: "('e \<leftrightarrow> 'f) \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction" and
  cHide          :: "('e, 's) cyphyaction \<Rightarrow> 'e set \<Rightarrow> ('e, 's) cyphyaction" and
  cParallelAct   :: "('a \<Longrightarrow> 's) \<Rightarrow> ('b \<Longrightarrow> 's) \<Rightarrow> 'e set \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction" and
  cParallel      :: "'e set \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction" and
  cInterrupt     :: "('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction"

axiomatization
  cEvolve        :: "('a::real_normed_vector \<Longrightarrow> 's) \<Rightarrow> ('s \<Rightarrow> 's) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('e, 's) cyphyaction" and
  cInterruptCond :: "('e, 's) cyphyaction \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('e, 's) cyphyaction" and
  cTimeout       :: "('e, 's) cyphyaction \<Rightarrow> ('s \<Rightarrow> real) \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction"

definition cSkip :: "('e, 's) cyphyaction" where
"cSkip = cAssigns id"

adhoc_overloading 
  useq \<rightleftharpoons> cSeq and
  uassigns \<rightleftharpoons> cAssigns and
  ucond \<rightleftharpoons> cCond and
  ualtern_list \<rightleftharpoons> "cAlternList" and
  Skip \<rightleftharpoons> cSkip and
  Stop \<rightleftharpoons> cStop and
  Guard \<rightleftharpoons> cGuard and
  ExtChoice \<rightleftharpoons> cExtChoice and
  InputPrefix \<rightleftharpoons> cInputPrefix and
  OutputPrefix \<rightleftharpoons> cOutputPrefix and
  SyncPrefix \<rightleftharpoons> cSyncPrefix and
  Interrupt \<rightleftharpoons> cInterrupt and
  Rename \<rightleftharpoons> cRename and
  Hide \<rightleftharpoons> cHide and
  Parallel \<rightleftharpoons> cParallel and
  ParallelAct \<rightleftharpoons> cParallelAct and
  Evolve \<rightleftharpoons> cEvolve and
  Timeout \<rightleftharpoons> cTimeout and
  InterruptCond \<rightleftharpoons> cInterruptCond

subsection \<open> Axioms \<close>

axiomatization where
  cSeq_mono [mono_rule]: "\<lbrakk> P\<^sub>1 \<le> P\<^sub>2; Q\<^sub>1 \<le> Q\<^sub>2 \<rbrakk> \<Longrightarrow> cSeq P\<^sub>1 Q\<^sub>1 \<le> cSeq P\<^sub>2 Q\<^sub>2" and
  cExtChoice_mono [mono_rule]: "\<lbrakk> P\<^sub>1 \<le> P\<^sub>2; Q\<^sub>1 \<le> Q\<^sub>2 \<rbrakk> \<Longrightarrow> cExtChoice P\<^sub>1 Q\<^sub>1 \<le> cExtChoice P\<^sub>2 Q\<^sub>2" and
  cInput_mono [mono_rule]: "\<lbrakk> \<And> x::'a. (P x :: ('e, 's) cyphyaction) \<le> Q x \<rbrakk> \<Longrightarrow> c\<^bold>?x \<rightarrow> P x \<le> c\<^bold>?x \<rightarrow> Q x" and
  cEventPrefix_mono [mono_rule]: "R\<^sub>1 \<le> R\<^sub>2 \<Longrightarrow> cEventPrefix e R\<^sub>1 \<le> cEventPrefix e R\<^sub>2"

subsection \<open> Axiomatic CSP Step Laws \<close>


named_theorems ax_step_laws
  \<open>axiomatic CyPhyCircus step laws\<close>



axiomatization where
  ax_cSync_event_prefix [ax_step_laws]:
    "cSyncPrefix c P = cEventPrefix (evsimple c) P" and
  ax_cOutput_event_prefix [ax_step_laws]:
    "cOutputPrefix d (\<lambda> s. v) Q = cEventPrefix (build\<^bsub>d\<^esub> v) Q"

text \<open> Step laws for sequential composition (Roscoe, ch.\ 6). \<close>

axiomatization where
  ax_cSeq_event_prefix [ax_step_laws]:
    "cSeq (cEventPrefix e P) Q = cEventPrefix e (cSeq P Q)" and
  ax_cSeq_skip_left [ax_step_laws]:
    "cSeq cSkip P = P" and
  ax_cSeq_skip_right [ax_step_laws]:
    "cSeq P cSkip = P" and
  ax_cSeq_stop_left [ax_step_laws]:
    "cSeq cStop P = cStop" and
  ax_cSeq_assoc [ax_step_laws]:
    "cSeq (cSeq P Q) R = cSeq P (cSeq Q R)"

text \<open>
  Step laws for external choice
\<close>

axiomatization where
  ax_cExtChoice_stop_left [ax_step_laws]:
    "cExtChoice cStop P = P" and
  ax_cExtChoice_idem [ax_step_laws]:
    "cExtChoice P P = P" and
  ax_cExtChoice_assoc [ax_step_laws]:
    "cExtChoice (cExtChoice P Q) R = cExtChoice P (cExtChoice Q R)" and
  ax_cExtChoice_comm:
    "cExtChoice P Q = cExtChoice Q P"

lemma ax_cExtChoice_stop_right [ax_step_laws]:
  "cExtChoice P cStop = P"
  by (metis ax_cExtChoice_comm ax_cExtChoice_stop_left)

unbundle Circus_Syntax

declare [[literal_variables]]

notation useq (infixr ";" 55)

end
