theory Codegen
  imports Axiomatic_CyPhyCircus.Ax_CyPhyCircus
    "ITree_Simulation.Code_Target_Rational" Interaction_Trees.ITree_Extraction
    "HOL-Library.Multiset" "Framed_ODEs.Framed_ODEs" (*"HOL-Library.Code_Real_Approx_By_Float"*)
    "HOL-Library.AList"
begin

unbundle Circus_Syntax
unbundle no UTP_Syntax
unbundle maplet_syntax

no_notation Abstract_Prog_Syntax.useq (infixr ";" 55)

(* add some missing monotonicity axioms (needs moving to Axiomatic_CyPhyCircus.Ax_CyPhyCircus) *)
axiomatization where
  cSync_mono [mono_rule]: "\<lbrakk> P\<^sub>1 \<le> P\<^sub>2 \<rbrakk> \<Longrightarrow> c \<rightarrow> P\<^sub>1 \<le> c \<rightarrow> P\<^sub>2" and
  cInput_mono [mono_rule]: "\<lbrakk>\<And>x. F\<^sub>1 x \<le> F\<^sub>2 x \<rbrakk> \<Longrightarrow> c'\<^bold>?x \<rightarrow> F\<^sub>1 x \<le> c'\<^bold>?x \<rightarrow> F\<^sub>2 x" and
  cOutput_mono [mono_rule]: "\<lbrakk> P\<^sub>1 \<le> P\<^sub>2 \<rbrakk> \<Longrightarrow> cOutputPrefix c' e P\<^sub>1 \<le> cOutputPrefix c' e P\<^sub>2"
for c :: "unit \<Longrightarrow>\<^sub>\<triangle> 'e"
and c' :: "'a \<Longrightarrow>\<^sub>\<triangle> 'e"
and F\<^sub>1 F\<^sub>2 :: "'a \<Rightarrow> ('e, 's) cyphyaction"
and P\<^sub>1 P\<^sub>2 :: "('e, 's) cyphyaction"
and e :: "'s \<Rightarrow> 'a"

section \<open>Miscellaneous Codegen Setup\<close>

lemma pfun_lookup_map_code [code]:
  "pfun_lookup (pfun_of_map f) k = f k"
  by auto

lemma Fract_code [code]:
  "Fract a b = (if b = 0 then 0 else rat_of_rational (Frct_integer (integer_of_int a, integer_of_int b)))"
  by (cases "b = 0", simp_all add: rat_number_collapse Rat.of_int_def sym[OF divide_integer_rational]
        divide_rational.rep_eq sym[OF rat_of_int_int_of_integer] Fract_of_int_quotient)

ML \<open>val rationalT = @{typ rational}\<close>
ML \<open>val integerT = @{typ integer}\<close>


code_printing
  type_constructor rational \<rightharpoonup> (SML) "Rat.rat"
  | class_instance rational :: "HOL.equal" \<rightharpoonup> (SML) -
  | constant "0 :: rational" \<rightharpoonup> (SML) "(Rat.of'_int 0)"
  | constant "1 :: rational" \<rightharpoonup> (SML) "(Rat.of'_int 1)"
  | constant "Code_Rational.term_of_rational_inst.term_of_rational" \<rightharpoonup>
    (SML) "(fn r => let val num = HOLogic.mk'_number integerT (fst (Rat.dest r))
                        val den = HOLogic.mk'_number integerT (snd (Rat.dest r))
                        val pair = HOLogic.mk'_prod (num, den)
                    in Const (\"Code'_Rational.Frct'_integer\",(HOLogic.mk'_prodT (integerT, integerT)) --> rationalT) $ pair
                    end)"
  | constant "Frct_integer" \<rightharpoonup> (SML) "Rat.make (_)"
  | constant "HOL.equal :: rational \<Rightarrow> rational \<Rightarrow> bool" \<rightharpoonup>
    (SML) "(_) = (_)"
  |  constant "(<) :: rational \<Rightarrow> rational \<Rightarrow> bool" \<rightharpoonup>
    (SML) "Rat.lt (_) (_)"
  |  constant "(\<le>) :: rational \<Rightarrow> rational \<Rightarrow> bool" \<rightharpoonup>
    (SML) "Rat.le (_) (_)"
  | constant "(+) :: rational \<Rightarrow> rational \<Rightarrow> rational" \<rightharpoonup>
    (SML) "Rat.add (_) (_)"
  | constant "(-) :: rational \<Rightarrow> rational \<Rightarrow> rational" \<rightharpoonup>
    (SML) "Rat.add (_) (Rat.neg (_))"
  | constant "(*) :: rational \<Rightarrow> rational \<Rightarrow> rational" \<rightharpoonup>
    (SML) "Rat.mult (_) (_)"
  | constant "(/) :: rational \<Rightarrow> rational \<Rightarrow> rational" \<rightharpoonup>
    (SML) "Rat.mult (_) (Rat.inv (_))"
  | constant "inverse :: rational \<Rightarrow> rational" \<rightharpoonup>
    (SML) "Rat.inv (_)"
 | constant "uminus :: rational \<Rightarrow> rational" \<rightharpoonup>
    (SML) "Rat.neg (_)"

find_theorems "divide (Ratreal ?a) (Ratreal ?b)"

code_printing
  constant numerator \<rightharpoonup> (SML) "(fst o Rat.dest)"
  | constant denominator \<rightharpoonup> (SML) "(snd o Rat.dest)"


ML \<open>fun digits_to_int [] = 0
      | digits_to_int (x :: xs) = 10 * (digits_to_int xs) + x\<close>
ML \<open>fun intpow x n = if n <= 0 then 1 else x * (intpow x (n-1))\<close>
ML \<open>fun realpow x n = if n <= 0 then 1.0 else x * (realpow x (n-1))\<close>

(*code_printing
  constant "integer_power" \<rightharpoonup> (SML) "realpow"*)

ML \<open>fun term_of_real r =
      let
        val {digits = xs, exp = n, sign = s, ...} = Real.toDecimal r;
        val exp = Const (@{const_name Power.power}, HOLogic.realT --> HOLogic.natT --> HOLogic.realT);
        val ten = HOLogic.mk_number HOLogic.realT 10;
        val n = if length xs > n then n - (length xs) else if null xs then n else n - 1
        val exp10 = if (abs n) = 1 then ten else exp $ ten $ HOLogic.mk_number HOLogic.natT (abs n);
        val mant = if s then ~(digits_to_int xs) else digits_to_int xs
        val mant_t = HOLogic.mk_number HOLogic.realT (if n >= 0 then mant * (intpow 10 n) else mant)
      in if n >= 0 then mant_t else  @{term Real.divide_real_inst.divide_real} $ mant_t $ exp10 end\<close>

ML \<open>val set_real_float_printings =
      let val real_tyco = #1 (Code_Printer.parse_tyco_syntax [Token.make_string0 "Real.real"])
          val real_tyco_pr = Code_Symbol.Type_Constructor (@{type_name real}, [("Eval", SOME (real_tyco))])
          val Ratreal_const = Code_Printer.plain_const_syntax "(fn Rat_of_rational r => let val (p, q) = Rat.dest r in (Real.fromLargeInt p) / (Real.fromLargeInt q) end)"
          val Ratreal_const_pr = Code_Symbol.Constant (@{const_name Ratreal}, [("Eval", SOME (Ratreal_const))])
          val plus_const = Code_Printer.plain_const_syntax "curry Real.+"
          val plus_const_pr = Code_Symbol.Constant (@{const_name Real.plus_real_inst.plus_real}, [("Eval", SOME (plus_const))])
          val minus_const = Code_Printer.plain_const_syntax "curry Real.-"
          val minus_const_pr = Code_Symbol.Constant (@{const_name Real.minus_real_inst.minus_real}, [("Eval", SOME (minus_const))])
          val times_const = Code_Printer.plain_const_syntax "curry Real.*"
          val times_const_pr = Code_Symbol.Constant (@{const_name Real.times_real_inst.times_real}, [("Eval", SOME (times_const))])
          val divide_const = Code_Printer.plain_const_syntax "curry Real./"
          val divide_const_pr = Code_Symbol.Constant (@{const_name Real.divide_real_inst.divide_real}, [("Eval", SOME (divide_const))])
          val inverse_const = Code_Printer.plain_const_syntax "(curry Real./ (Real.fromInt 1))"
          val inverse_const_pr = Code_Symbol.Constant (@{const_name Real.inverse_real_inst.inverse_real}, [("Eval", SOME (inverse_const))])
          val uminus_const = Code_Printer.plain_const_syntax "Real.~"
          val uminus_const_pr = Code_Symbol.Constant (@{const_name Real.uminus_real_inst.uminus_real}, [("Eval", SOME (uminus_const))])
          val zero_const = Code_Printer.plain_const_syntax "(Real.fromInt 0)"
          val zero_const_pr = Code_Symbol.Constant (@{const_name Real.zero_real_inst.zero_real}, [("Eval", SOME (zero_const))])
          val one_const = Code_Printer.plain_const_syntax "(Real.fromInt 1)"
          val one_const_pr = Code_Symbol.Constant (@{const_name Real.one_real_inst.one_real}, [("Eval", SOME (one_const))])
          val term_of_const = Code_Printer.plain_const_syntax "term_of_real"
          val term_of_const_pr = Code_Symbol.Constant (@{const_name Real.term_of_real_inst.term_of_real}, [("Eval", SOME (term_of_const))])
          val printings = [
                real_tyco_pr,
                plus_const_pr,
                minus_const_pr,
                times_const_pr,
                uminus_const_pr,
                zero_const_pr,
                one_const_pr,
                term_of_const_pr,
                divide_const_pr,
                inverse_const_pr
              ]
      in fold Code_Target.set_printings printings end\<close>

lemma inverse_rat_of_rational [code]: 
  "inverse (rat_of_rational x) = rat_of_rational (inverse x)"
  by (transfer, simp)

lemma integer_power_rat_of_rational [code]: 
  "integer_power (rat_of_rational x) n = rat_of_rational (integer_power x n)"
  unfolding integer_power_def by (transfer, simp)

lemma integer_power_Ratreal [code]: 
  "integer_power (Ratreal x) n = Ratreal (integer_power x n)"
  unfolding integer_power_def by (transfer, simp add: of_rat_power)

instantiation real :: default
begin

definition [code]: "default_real \<equiv> (0 :: real)"

instance by intro_classes
end

section \<open>cyphyaction as a code_datatype\<close>

abbreviation "RKstep f h y \<equiv>
  let k1 = f y;
      k2 = f (y + ((h / 2) *\<^sub>R k1));
      k3 = f (y + ((h / 2) *\<^sub>R k2));
      k4 = f (y + h *\<^sub>R k3)
  in y + (h / 6) *\<^sub>R (k1 + 2*\<^sub>Rk2 + 2*\<^sub>Rk3 + k4)"

class recursive_system = complete_lattice +
  fixes bottom :: 'a
    and total_actions :: "'a itself \<Rightarrow> nat"
begin end

instantiation cyphyaction ::  (type,type) recursive_system 
begin
definition [code_unfold]: "bottom_cyphyaction \<equiv> cChaos"
definition total_actions_cyphyaction :: "('a, 'b) cyphyaction itself \<Rightarrow> \<nat>" where
  [code_unfold]: "total_actions_cyphyaction _ \<equiv> (1::nat)"
instance ..
end

instantiation prod ::  (recursive_system,recursive_system) recursive_system 
begin
definition [code_unfold]: "bottom_prod \<equiv> (bottom, bottom)"
definition total_actions_prod :: "('a \<times> 'b) itself \<Rightarrow> \<nat>" where
  [code_unfold]: "total_actions_prod _ \<equiv> (total_actions TYPE('a)) + (total_actions TYPE('b))"
instance ..
end

axiomatization
  cEvolve' :: "(real \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('e, 's) cyphyaction" and
  cInputPrefix' :: "('e \<Rightarrow> (('s \<Rightarrow> \<bool>) \<times> ('e, 's) cyphyaction) option) \<Rightarrow> ('e, 's) cyphyaction" and
  cOutputPrefix' :: "('s \<Rightarrow> 'e) \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction" and
  cParallelAct' :: "('s \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> 'e set \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction" and
  cRec' :: "nat \<Rightarrow> (nat \<Rightarrow> ('e, 's) cyphyaction) \<Rightarrow> ('e, 's) cyphyaction" and
  cRename' :: "('e \<leftrightarrow> 'e) \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction"
where
  cEvolve_cEvolve'[code_unfold]:
    "cEvolve v f p \<equiv> cEvolve' (\<lambda>r s. put\<^bsub>v\<^esub> s (RKstep (\<lambda>x. get\<^bsub>v\<^esub> (f (put\<^bsub>v\<^esub> s x))) r (get\<^bsub>v\<^esub> s))) p" and
  cInputPrefix_cInputPrefix'[code_unfold]:
    "cInputPrefix c S F \<equiv> cInputPrefix' (\<lambda>e.  map_option F ((match\<^bsub>c\<^esub> e) \<bind> (map_id_on S)))" and
  cOutputPrefix_cOutputPrefix'[code_unfold]:
    "cOutputPrefix c expr P \<equiv> cOutputPrefix' (build\<^bsub>c\<^esub> \<circ> expr) P" and
  cParallelAct_cParallelAct'[code_unfold]:
    "cParallelAct ns1 ns2 cs P Q \<equiv> cParallelAct' (\<lambda> s0 s1 s2. s0 \<triangleleft>\<^bsub>ns1\<^esub> s1 \<triangleleft>\<^bsub>ns2\<^esub> s2) cs P Q" and
  nu_cRec'1[code_unfold]:
    "\<nu> FF \<equiv> cRec' (total_actions TYPE(('e, 's) cyphyaction)) (\<lambda>n. Nat.funpow n FF bottom)" and
  nu_cRec'2[code_unfold]:
    "g (\<nu> FF') \<equiv> cRec' (total_actions TYPE('p)) (\<lambda>n. g (Nat.funpow n FF' bottom))" and
  cRename_cRename'[code_unfold]:
    "cRename rel P = cRename' rel P"
  for v :: "'b :: real_normed_vector \<Longrightarrow> 's"
and FF :: "('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction"
and FF' :: "'p::recursive_system \<Rightarrow> 'p::recursive_system"
and g :: "'p \<Rightarrow> ('e, 's) cyphyaction"
and f :: "'s \<Rightarrow> 's"
and p :: "'s \<Rightarrow> bool"

named_theorems cyphyaction_datatype_unfolds 
lemmas [cyphyaction_datatype_unfolds] = cEvolve_cEvolve' cInputPrefix_cInputPrefix' cOutputPrefix_cOutputPrefix' cParallelAct_cParallelAct' nu_cRec'1 nu_cRec'2

code_datatype cSkip cAssigns cStop cChaos cAssume cEvolve' cSyncPrefix cOutputPrefix' cInputPrefix'
  cSeq cGuard cCond "inf :: ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction"
  cExtChoice cParallelAct' cRec' cHide cRename'

section \<open>Operational semantics for trace checking\<close>

datatype 'e visibility = Visible 'e | Hidden nat 'e

datatype ('e, 's) cyphystep =
  Termination 's
  | Timestep 's bool "('e, 's) cyphyaction"
  | StUpd 's "('e, 's) cyphyaction"
  | EventStep "('e, 's) cyphyaction"

fun is_Timestep where "is_Timestep (Timestep s strict P) = True" | "is_Timestep _ = False"
fun is_Termination where "is_Termination (Termination s) = True" | "is_Termination _ = False"
fun is_StUpd where "is_StUpd (StUpd s P) = True" | "is_StUpd _ = False"
fun is_EventStep where "is_EventStep (EventStep P) = True" | "is_EventStep _ = False"

fun map_cyphystep_continuation :: "(('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction) \<Rightarrow> ('e, 's) cyphystep \<Rightarrow> ('e, 's) cyphystep" where
  "map_cyphystep_continuation f (Termination s) = Termination s"
| "map_cyphystep_continuation f (Timestep s b P) = Timestep s b (f P)"
| "map_cyphystep_continuation f (StUpd s P) = StUpd s (f P)"
| "map_cyphystep_continuation f (EventStep P) = EventStep (f P)"

fun rapply_alist :: "('a \<times> 'b) list \<Rightarrow> 'b \<Rightarrow> 'a list" where
  "rapply_alist [] b = []"
| "rapply_alist ((x, y) # xs) b = (if b = y then [x] else []) @ rapply_alist xs b"


fun group_cyphysteps :: "('e, 's) cyphystep list  \<Rightarrow>
    's list
      \<times> ('s \<times> bool \<times> ('e, 's) cyphyaction) list
      \<times> ('s \<times> ('e, 's) cyphyaction) list
      \<times> ('e, 's) cyphyaction list" where
  "group_cyphysteps [] = ([], [], [], [])"
| "group_cyphysteps (Termination s # steps) = apfst ((#) s) (group_cyphysteps steps)"
| "group_cyphysteps (Timestep s strict P # steps) = apsnd (apfst ((#) (s, strict, P))) (group_cyphysteps steps)"
| "group_cyphysteps (StUpd s P # steps) = apsnd (apsnd (apfst ((#) (s, P)))) (group_cyphysteps steps)"
| "group_cyphysteps (EventStep P # steps) = apsnd (apsnd (apsnd ((#) P))) (group_cyphysteps steps)"

axiomatization
  step_cyphyaction :: "real \<Rightarrow> nat \<Rightarrow> 'e visibility list \<Rightarrow> 's \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphystep list option"
  where
  step_cyphyaction_cAssigns[code]: (* terminate immediately with updated state *)
    "step_cyphyaction timestep n t s (cAssigns subst) = Some [Termination (subst s)]" and
  step_cyphyaction_cStop[code]: (* deadlock without terminating - but allow time to pass *)
    "step_cyphyaction timestep n t s cStop = Some [Timestep s False cStop]" and
  step_cyphyaction_cChaos[code]: (* error out of checking *)
    "step_cyphyaction timestep n t s cChaos = None" and
  step_cyphyaction_cAssume[code]: (* error out of checking if condition is false, terminate if true (behave as cSkip) *)
    "step_cyphyaction timestep n t s (cAssume pred)
      = (if pred s then step_cyphyaction timestep n t s cSkip else None)" and
  step_cyphyaction_cEvolve'[code]: (* terminate immediately if condition false, otherwise update according to solution and time passes *)
    "step_cyphyaction timestep n t s (cEvolve' sol pred)
      = Some (if pred s then [Timestep (sol timestep s) True (cEvolve' sol pred)] else [Termination s] )" and
  step_cyphyaction_cSyncPrefix1[code]: (* no event means checking fails - but time could still pass (and perhaps lead to termination) *)
    "step_cyphyaction timestep n [] s (cSyncPrefix e P) = Some [Timestep s False (cSyncPrefix e P)]" and
  step_cyphyaction_cSyncPrefix2[code]: (* check if event is correct, also allow time to pass *)
    "step_cyphyaction timestep n (Visible te # t) s (cSyncPrefix e P)
      = (if te = build\<^bsub>e\<^esub> () then Some [EventStep P, Timestep s False (cSyncPrefix e P)] else Some [Timestep s False (cSyncPrefix e P)] )" and
  step_cyphyaction_cSyncPrefix3[code]: (* an event prefixing can't produce a hidden event, but does allow time to pass *)
    "step_cyphyaction timestep n (Hidden depth te # t) s (cSyncPrefix e P) = Some [Timestep s False (cSyncPrefix e P)]" and
  step_cyphyaction_cOutputPrefix'1[code]: (* no event means checking fails - but time could still pass (and perhaps lead to termination)*)
    "step_cyphyaction timestep n [] s (cOutputPrefix' chexpr P) = Some [Timestep s False (cOutputPrefix' chexpr P)]" and
  step_cyphyaction_cOutputPrefix'2[code]: (* check if event is correct, also allow time to pass *)
    "step_cyphyaction timestep n (Visible te # t) s (cOutputPrefix' chexpr P)
      = (if chexpr s = te then Some [EventStep P, Timestep s False (cOutputPrefix' chexpr P)] else Some [Timestep s False (cOutputPrefix' chexpr P)] )" and
  step_cyphyaction_cOutputPrefix'3[code]: (* an output prefixing can't produce a hidden event, but does allow time to pass *)
    "step_cyphyaction timestep n (Hidden depth te # t) s (cOutputPrefix' chexpr P) = Some [Timestep s False (cOutputPrefix' chexpr P)]" and
  step_cyphyaction_cInputPrefix'1[code]: (* no event means checking fails - but time could still pass (and perhaps lead to termination) *)
    "step_cyphyaction timestep n [] s (cInputPrefix' F) = Some [Timestep s False (cInputPrefix' F)]" and
  step_cyphyaction_cInputPrefix'2[code]: (* check if event is correct, also allow time to pass *)
    "step_cyphyaction timestep n (Visible te # t) s (cInputPrefix' F)
      = (case F te of
          None \<Rightarrow> Some [Timestep s False (cInputPrefix' F)] \<comment> \<open>event not valid, deadlock\<close>
        | Some (pred, P) \<Rightarrow> \<comment> \<open>event is valid, but is the predicate true?\<close>
            if pred s then
              Some [EventStep P, Timestep s False (cInputPrefix' F)]
            else
              Some [Timestep s False (cInputPrefix' F)] \<comment> \<open> we can wait until the predicate is true \<close> )" and
  step_cyphyaction_cInputPrefix'3[code]: (* input prefixing cannot produce a hidden event *)
    "step_cyphyaction timestep n (Hidden depth te # t) s (cInputPrefix' F) = Some []" and
  step_cyphyaction_cSeq[code]: (* try the first, then proceed to the second after termination *)
    "step_cyphyaction timestep n t s (cSeq P Q) =
      (case (step_cyphyaction timestep n t s P) of
          Some xs \<Rightarrow>
            Some (map
              (\<lambda> step. case step of
                  Termination s' \<Rightarrow> StUpd s' Q
                | Timestep s' strict P' \<Rightarrow> Timestep s' strict (cSeq P' Q)
                | StUpd s' P' \<Rightarrow> StUpd s' (cSeq P' Q)
                | EventStep P' \<Rightarrow> EventStep (cSeq P' Q))
              xs)
        | None \<Rightarrow> None)" and
  step_cyphyaction_cGuard[code]: (* deadlock if predicate is false, otherwise behave as inner action*)
    "step_cyphyaction timestep n t s (cGuard pred P)
      = (if pred s then step_cyphyaction timestep n t s P else Some [Timestep s False cStop] )" and
  step_cyphyaction_cCond[code]: (* behave as either inner action depending on predicate*)
    "step_cyphyaction timestep n t s (cCond P pred Q)
      = (if pred s then step_cyphyaction timestep n t s P else step_cyphyaction timestep n t s Q)" and
  step_cyphyaction_cInterruptCond: (* terminate immediately if the predicate is true, otherwise continue the inner action without resolving the interrupt *)
    "step_cyphyaction timestep n t s (cInterruptCond P pred) =
      (if pred s then
        step_cyphyaction timestep n t s cSkip
      else
        map_option
          (map (map_cyphystep_continuation (\<lambda>P'. cInterruptCond P' pred)))
          (step_cyphyaction timestep n t s P))" and
  step_cyphyaction_cTimeout: (* behave as Q if the deadline has expires is true, otherwise continue P without, reducing the deadline *)
    "step_cyphyaction timestep n t s (cTimeout P sn Q) =
      (if sn s = 0 then
        step_cyphyaction timestep n t s Q
      else
        map_option
          (map (map_cyphystep_continuation (\<lambda>P'. cTimeout P' (\<lambda>s. sn s - timestep) Q)))
          (step_cyphyaction timestep n t s P))" and
  step_cyphyaction_inf[code]: (* evaluate both and concatenate results *)
    "step_cyphyaction timestep n t s (inf P Q)
      = (case (step_cyphyaction timestep n t s P, step_cyphyaction timestep n t s Q) of
          (Some xs, Some ys) \<Rightarrow> Some (xs @ ys)
        | (None, Some ys) \<Rightarrow> Some ys
        | (Some xs, None) \<Rightarrow> Some xs
        | (None, None) \<Rightarrow> None)" and
  step_cyphyaction_cExtChoice[code]: (* synchronise timesteps, concatenate choices *)
    "step_cyphyaction timestep n t s (cExtChoice P Q)
      = (case (step_cyphyaction timestep n t s P, step_cyphyaction timestep n t s Q) of
          (Some xs, Some ys) \<Rightarrow>
            \<comment> \<open>a timestep that doesn't change the state doesn't resolve the choice\<close>
            Some (case (List.partition (\<lambda> step. case step of Timestep s' strict _ \<Rightarrow> s' = s | _ \<Rightarrow> False) xs,
                        List.partition (\<lambda> step. case step of Timestep s' strict _ \<Rightarrow> s' = s | _ \<Rightarrow> False) ys) of
              ((xs_ts, xs), (ys_ts, ys)) \<Rightarrow>
               xs @ ys @
                \<comment> \<open>merge timesteps\<close>
                (map
                  (\<lambda> (x, y). case (x, y) of (Timestep _ strict1 P', Timestep _ strict2 Q') \<Rightarrow>
                    Timestep s (disj strict1 strict2) (cExtChoice P' Q'))
                  (List.product xs_ts ys_ts)))
        | _ \<Rightarrow> None \<comment> \<open>if either side diverges, the whole thing does\<close>)" and
  step_cyphyaction_cParallelAct'1[code]: (* no event to merge, synchronise timesteps and termination *)
    "step_cyphyaction timestep n [] s (cParallelAct' mrg cs P Q)
      = (case (map_option group_cyphysteps (step_cyphyaction timestep n [] s P),
                map_option group_cyphysteps (step_cyphyaction timestep n [] s Q)) of
              (Some (P_terms, P_timesteps, P_stupds, P_eventsteps),
                Some (Q_terms, Q_timesteps, Q_stupds, Q_eventsteps)) \<Rightarrow>
                        Some (
                          \<comment> \<open>unsynchronised steps evolve one side, merging the state\<close>
                          (map (\<lambda> P'. EventStep (cParallelAct' mrg cs P' Q)) P_eventsteps)
                          @ (map (\<lambda> Q'. EventStep (cParallelAct' mrg cs P Q')) Q_eventsteps)
                          @ (map (\<lambda> (s', P'). StUpd (mrg s s' s) (cParallelAct' mrg cs P' Q)) P_stupds)
                          @ (map (\<lambda> (s', Q'). StUpd (mrg s s s') (cParallelAct' mrg cs P Q')) Q_stupds)
                          \<comment> \<open>terminations are synchronised, merging the state\<close>
                          @ (map (\<lambda>(s1, s2). Termination (mrg s s1 s2)) (List.product P_terms Q_terms))
                          \<comment> \<open>timesteps are synchronised, merging the state\<close>
                          @ (map (\<lambda>((s1, strict1, P'), (s2, strict2, Q')). 
                                Timestep (mrg s s1 s2) (disj strict1 strict2) (cParallelAct' mrg cs P' Q'))
                              (List.product P_timesteps Q_timesteps))
                          \<comment> \<open>timesteps can synchronise with a termination, merging the state\<close>
                          @ (map (\<lambda>((s1, strict1, P'), (s2)). 
                                Timestep (mrg s s1 s2) strict1 (cParallelAct' mrg cs P' cSkip))
                              (List.product P_timesteps Q_terms))
                          @ (map (\<lambda>((s1), (s2, strict2, Q')). 
                                Timestep (mrg s s1 s2) strict2 (cParallelAct' mrg cs cSkip Q'))
                              (List.product P_terms Q_timesteps)))
            | _ \<Rightarrow> None \<comment> \<open>if either side diverges, the whole thing does\<close>)" and
  step_cyphyaction_cParallelAct'2[code]: (* hidden events are unsynchronised, synchronise timesteps and termination *)
    "step_cyphyaction timestep n (Hidden depth te # t) s (cParallelAct' mrg cs P Q)
      = (case (map_option group_cyphysteps (step_cyphyaction timestep n (Hidden depth te # t) s P),
                map_option group_cyphysteps (step_cyphyaction timestep n (Hidden depth te # t) s Q)) of
              (Some (P_terms, P_timesteps, P_stupds, P_eventsteps),
                Some (Q_terms, Q_timesteps, Q_stupds, Q_eventsteps)) \<Rightarrow>
                        Some (
                          \<comment> \<open>unsynchronised steps evolve one side, merging the state\<close>
                          (map (\<lambda> P'. EventStep (cParallelAct' mrg cs P' Q)) P_eventsteps)
                          @ (map (\<lambda> Q'. EventStep (cParallelAct' mrg cs P Q')) Q_eventsteps)
                          @ (map (\<lambda> (s', P'). StUpd (mrg s s' s) (cParallelAct' mrg cs P' Q)) P_stupds)
                          @ (map (\<lambda> (s', Q'). StUpd (mrg s s s') (cParallelAct' mrg cs P Q')) Q_stupds)
                          \<comment> \<open>terminations are synchronised, merging the state\<close>
                          @ (map (\<lambda>(s1, s2). Termination (mrg s s1 s2)) (List.product P_terms Q_terms))
                          \<comment> \<open>timesteps are synchronised, merging the state\<close>
                          @ (map (\<lambda>((s1, strict1, P'), (s2, strict2, Q')). 
                                Timestep (mrg s s1 s2) (disj strict1 strict2) (cParallelAct' mrg cs P' Q'))
                              (List.product P_timesteps Q_timesteps))
                          \<comment> \<open>timesteps can synchronise with a termination, merging the state\<close>
                          @ (map (\<lambda>((s1, strict1, P'), (s2)). 
                                Timestep (mrg s s1 s2) strict1 (cParallelAct' mrg cs P' cSkip))
                              (List.product P_timesteps Q_terms))
                          @ (map (\<lambda>((s1), (s2, strict2, Q')). 
                                Timestep (mrg s s1 s2) strict2 (cParallelAct' mrg cs cSkip Q'))
                              (List.product P_terms Q_timesteps)))
            | _ \<Rightarrow> None \<comment> \<open>if either side diverges, the whole thing does\<close>)" and
  step_cyphyaction_cParallelAct'3[code]: (* visible events are handled depending on the synchronisation set, synchronise timesteps and termination *)
    "step_cyphyaction timestep n (Visible te # t) s (cParallelAct' mrg cs P Q)
      = (case (map_option group_cyphysteps (step_cyphyaction timestep n (Visible te # t) s P),
                map_option group_cyphysteps (step_cyphyaction timestep n (Visible te # t) s Q)) of
              (Some (P_terms, P_timesteps, P_stupds, P_eventsteps),
                Some (Q_terms, Q_timesteps, Q_stupds, Q_eventsteps)) \<Rightarrow>
                        Some (
                          \<comment> \<open>check for whether we need to synchronise the event steps\<close>
                          (if te \<in> cs then
                            map (\<lambda> (P', Q'). EventStep (cParallelAct' mrg cs P' Q')) (List.product P_eventsteps Q_eventsteps)
                          else
                            (map (\<lambda> P'. EventStep (cParallelAct' mrg cs P' Q)) P_eventsteps)
                            @ (map (\<lambda> Q'. EventStep (cParallelAct' mrg cs P Q')) Q_eventsteps))
                          \<comment> \<open>unsynchronised steps evolve one side, merging the state\<close>
                          @ (map (\<lambda> (s', P'). StUpd (mrg s s' s) (cParallelAct' mrg cs P' Q)) P_stupds)
                          @ (map (\<lambda> (s', Q'). StUpd (mrg s s s') (cParallelAct' mrg cs P Q')) Q_stupds)
                          \<comment> \<open>terminations are synchronised, merging the state\<close>
                          @ (map (\<lambda>(s1, s2). Termination (mrg s s1 s2)) (List.product P_terms Q_terms))
                          \<comment> \<open>timesteps are synchronised, merging the state\<close>
                          @ (map (\<lambda>((s1, strict1, P'), (s2, strict2, Q')). 
                                Timestep (mrg s s1 s2) (disj strict1 strict2) (cParallelAct' mrg cs P' Q'))
                              (List.product P_timesteps Q_timesteps))
                          \<comment> \<open>timesteps can synchronise with a termination, merging the state\<close>
                          @ (map (\<lambda>((s1, strict1, P'), (s2)). 
                                Timestep (mrg s s1 s2) strict1 (cParallelAct' mrg cs P' cSkip))
                              (List.product P_timesteps Q_terms))
                          @ (map (\<lambda>((s1), (s2, strict2, Q')). 
                                Timestep (mrg s s1 s2) strict2 (cParallelAct' mrg cs cSkip Q'))
                              (List.product P_terms Q_timesteps)))
            | _ \<Rightarrow> None \<comment> \<open>if either side diverges, the whole thing does\<close>)" and
  step_cyphyaction_cRec'[code]: (* unroll the loop at least enough to match the trace *)
    "step_cyphyaction timestep n t s (cRec' m FF)
      = step_cyphyaction timestep n t s (FF (m * n))" and
  step_cyphyaction_cHide1[code]: (* if there are no events in the trace, just ignore hiding *)
    "step_cyphyaction timestep n [] s (cHide P S)
      = map_option (map (map_cyphystep_continuation (\<lambda>P. cHide P S))) (step_cyphyaction timestep n [] s P)" and
  step_cyphyaction_cHide2[code]: (* visible events in the hidden set can't happen under the hiding *)
    "step_cyphyaction timestep n (Visible te # t) s (cHide P S)
      = map_option (map (map_cyphystep_continuation (\<lambda>P. cHide P S))) 
          (if te \<in> S then 
            map_option (filter (Not \<circ> is_EventStep)) (step_cyphyaction timestep n (Visible te # t) s P)
          else
            step_cyphyaction timestep n (Visible te # t) s P)" and
  step_cyphyaction_cHide3[code]: (* hidden events in the hidden set are made visible - if they occur they need to be hidden again *)
    "step_cyphyaction timestep n (Hidden depth te # t) s (cHide P S)
      = map_option (map (map_cyphystep_continuation (\<lambda>P. cHide P S)))
          (if te \<in> S then
            case depth of
              0 \<Rightarrow> step_cyphyaction timestep n (Visible te # t) s P
            | Suc depth \<Rightarrow> step_cyphyaction timestep n (Hidden depth te # t) s P
        else
          step_cyphyaction timestep n (Hidden depth te # t) s P)" and
  step_cyphyaction_cRename'1[code]: (* if there are no events in the trace, just ignore renaming *)
    "step_cyphyaction timestep n [] s (cRename' (rel::'e \<leftrightarrow> 'e) P)
      = map_option (map (map_cyphystep_continuation (cRename' rel))) (step_cyphyaction timestep n [] s P)" and
  step_cyphyaction_cRename'2[code]: (* a hidden event can't be renamed *)
    "step_cyphyaction timestep n (Hidden depth te # t) s (cRename' (rel::'e \<leftrightarrow> 'e) P)
      = map_option (map (map_cyphystep_continuation (cRename' rel))) (step_cyphyaction timestep n (Hidden depth te # t) s P)" and
  step_cyphyaction_cRename'3[code]: (* a visible event is reverse-renamed and then renamed back in the result *)
    "step_cyphyaction timestep n (Visible te # t) s (cRename' (set alist :: 'e \<leftrightarrow> 'e) P)
      = map_option (map (map_cyphystep_continuation (cRename' (set alist)))) 
          (if list_ex ((=) te o snd) alist then
            fold (\<lambda>te'. combine_options (@) (step_cyphyaction timestep n (Visible te' # t) s P))
              (rapply_alist alist te)
              None
        else
          step_cyphyaction timestep n (Visible te # t) s P)"

lemma step_cyphyaction_cSkip[code]:
    "step_cyphyaction timestep n t s cSkip = Some [Termination s]"
  unfolding cSkip_def step_cyphyaction_cAssigns by simp

section \<open>Lifting the operational semantics to trace checking\<close>

fun expand_cyphyaction_step :: "'e visibility list \<Rightarrow> 's \<Rightarrow> ('e, 's) cyphystep list \<Rightarrow> ('s \<times> 'e visibility list \<times> ('e, 's) cyphyaction option) list" where
  "expand_cyphyaction_step t s [] = []"
| "expand_cyphyaction_step t s (Termination s' # steps) = (s', t, None) # expand_cyphyaction_step t s steps"
| "expand_cyphyaction_step t s (Timestep s' False P # steps) = expand_cyphyaction_step t s steps"
| "expand_cyphyaction_step t s (Timestep s' True P # steps) = (s', t, Some P) # expand_cyphyaction_step t s steps"
| "expand_cyphyaction_step t s (StUpd s' P # steps) = (s', t, Some P) # expand_cyphyaction_step t s steps"
| "expand_cyphyaction_step t s (EventStep P # steps) = (s, tl t, Some P) # expand_cyphyaction_step t s steps"

fun lift_cyphyaction_step :: "nat \<Rightarrow> real \<Rightarrow>
      ('s \<times> 'e visibility list \<times> ('e, 's) cyphyaction option)
        \<Rightarrow> ('s \<times> 'e visibility list \<times> ('e, 's) cyphyaction option) list option" where
  "lift_cyphyaction_step n ts (s, t, None) = Some [(s, t, None)]"
| "lift_cyphyaction_step n ts (s, t, Some P) = map_option (expand_cyphyaction_step t s) (step_cyphyaction ts n t s P)"

fun option_list_bind :: "'a list option \<Rightarrow> ('a \<Rightarrow> 'b list option) \<Rightarrow> 'b list option" where
  "option_list_bind None f = None"
| "option_list_bind (Some []) f = Some []"
| "option_list_bind (Some [x] ) f = f x"
| "option_list_bind (Some (x # xs)) f = combine_options (@) (f x) (option_list_bind (Some xs) f)"

(* checks through a trace, returning continuations if it has the trace, empty trace if not, None on divergence *)
fun cyphyaction_check_trace :: "nat \<Rightarrow> real \<Rightarrow> bool \<Rightarrow> ('s \<times> 'e visibility list \<times> ('e, 's) cyphyaction option)
        \<Rightarrow> ('s \<times> ('e, 's) cyphyaction option) list option" where
  "cyphyaction_check_trace n ts False (s, [], P_opt) = Some [(s, P_opt)]" (* everything has the empty trace *)
| "cyphyaction_check_trace n ts True (s, [], None) = Some [(s, None)]" (* a terminating process has a trace that is just tick *)
| "cyphyaction_check_trace n ts has_tick (s, e # t, None) = Some []" (* a terminating process can't do more events *)
| "cyphyaction_check_trace n ts has_tick (s, t, Some P) =
    (if n = 0 then
      None
    else
     option_list_bind
      (lift_cyphyaction_step (Suc n) ts (s, t, Some P))
      (cyphyaction_check_trace (n-1) ts has_tick))" (* if there is a next process, explore it *)

term "map_option hd \<circ> those"

fun cyphyaction_has_trace_incremental :: "nat \<Rightarrow> real \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> 'e visibility list \<Rightarrow> bool \<Rightarrow> 's \<Rightarrow> ('e visibility list \<times> bool) option" where
  "cyphyaction_has_trace_incremental n ts P [] False s = None"
| "cyphyaction_has_trace_incremental n ts P [] True s = 
    (case cyphyaction_check_trace n ts True (s, [], Some P) of
        None \<Rightarrow> Some ([], True)
      | Some [] \<Rightarrow> Some ([], True)
      | Some (step#steps) \<Rightarrow> None)"
| "cyphyaction_has_trace_incremental n ts P (e#t) has_tick s =
    (case cyphyaction_check_trace n ts False (s, [e], Some P) of
      None \<Rightarrow> None
    | Some [] \<Rightarrow> \<comment> \<open>failed, start creating a counterexample\<close>
        Some ([e], False)
    | Some (step#steps) \<Rightarrow> \<comment> \<open>succeeded, try the next ones\<close>
        (map_option hd \<circ> those)
          (map (\<lambda>(s', opt_P').
            case opt_P' of
              None \<Rightarrow> Some ([e], False) \<comment> \<open>this branch terminated, but we had more to search for, start creating a counterexample\<close>
            | Some P' \<Rightarrow> map_option (apfst ((#) e)) (cyphyaction_has_trace_incremental n ts P' t has_tick s'))
        (step#steps)))"

fun cyphyaction_has_visible_trace_incremental :: "nat \<Rightarrow> real \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> 'e list \<Rightarrow> bool \<Rightarrow> 's \<Rightarrow> ('e list \<times> bool) option" where
  "cyphyaction_has_visible_trace_incremental n ts P [] False s = None"
| "cyphyaction_has_visible_trace_incremental n ts P [] True s = 
    (case cyphyaction_check_trace n ts True (s, [], Some P) of
        None \<Rightarrow> Some ([], True)
      | Some [] \<Rightarrow> Some ([], True)
      | Some (step#steps) \<Rightarrow> None)"
| "cyphyaction_has_visible_trace_incremental n ts P (e#t) has_tick s =
    (case cyphyaction_check_trace n ts False (s, [Visible e], Some P) of
      None \<Rightarrow> None
    | Some [] \<Rightarrow> \<comment> \<open>failed, start creating a counterexample\<close>
        Some ([e], False)
    | Some (step#steps) \<Rightarrow> \<comment> \<open>succeeded, try the next ones\<close>
        (map_option hd \<circ> those)
          (map (\<lambda>(s', opt_P').
              case opt_P' of
                None \<Rightarrow> Some ([e], False) \<comment> \<open>this branch terminated, but we had more to search for, start creating a counterexample\<close>
              | Some P' \<Rightarrow> map_option (apfst ((#) e)) (cyphyaction_has_visible_trace_incremental n ts P' t has_tick s'))
          (step#steps)))"

section \<open>Lifting the trace checking over constant instantiations\<close>

(* want to check that there exists an instantiation of the constants that makes P have the given trace *)

fun cyphyaction_has_trace_incremental_insts :: "nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> (('a::full_exhaustive) \<Rightarrow> ('e, 's) cyphyaction) \<Rightarrow> (('a::full_exhaustive) \<Rightarrow> bool) \<Rightarrow> 'e visibility list \<Rightarrow> bool \<Rightarrow> 's \<Rightarrow> 'e visibility list \<Rightarrow> ('e visibility list \<times> bool) option" where
  "cyphyaction_has_trace_incremental_insts step_limit breadth ts P pred [] has_tick s to_check =
    (case full_exhaustive_class.full_exhaustive
        (\<lambda> (a, term).
          if pred a then
            case cyphyaction_has_trace_incremental step_limit ts (P a) to_check has_tick s of
              None \<Rightarrow> Some (True, []) \<comment> \<open>the process has the trace, stop checking\<close>
            | Some _ \<Rightarrow> None \<comment> \<open>the process doesn't have the trace, continue\<close>
          else
            None)
        (natural_of_nat breadth) of
          Some _ \<Rightarrow> None \<comment> \<open>we have the trace, but we are at the end\<close>
        | None \<Rightarrow> Some (to_check, has_tick))" 
| "cyphyaction_has_trace_incremental_insts step_limit breadth ts P pred (e#t) has_tick s to_check =
    (case full_exhaustive_class.full_exhaustive
        (\<lambda> (a, term).
          if pred a then
            case cyphyaction_has_trace_incremental step_limit ts (P a) (to_check @ [e] ) has_tick s of
              None \<Rightarrow> Some (True, []) \<comment> \<open>the process has the trace, stop checking\<close>
            | Some _ \<Rightarrow> None \<comment> \<open>the process doesn't have the trace, continue\<close>
          else
            None)
        (natural_of_nat breadth) of
          Some _ \<Rightarrow> \<comment> \<open>we have the trace, try the next event\<close>
            cyphyaction_has_trace_incremental_insts step_limit breadth ts P pred t has_tick s (to_check @ [e] )
        | None \<Rightarrow> Some (to_check, False))"

fun cyphyaction_has_visible_trace_incremental_insts
      :: "nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> (('a::full_exhaustive) \<Rightarrow> ('e, 's) cyphyaction) \<Rightarrow> (('a::full_exhaustive) \<Rightarrow> bool) \<Rightarrow> 'e list \<Rightarrow> bool \<Rightarrow> 's \<Rightarrow> 'e list \<Rightarrow> ('e list \<times> bool) option" where
  "cyphyaction_has_visible_trace_incremental_insts step_limit breadth ts P pred [] has_tick s to_check =
    (case full_exhaustive_class.full_exhaustive
        (\<lambda> (a, term).
          if pred a then
            case cyphyaction_has_visible_trace_incremental step_limit ts (P a) to_check has_tick s of
              None \<Rightarrow> Some (True, []) \<comment> \<open>the process has the trace, stop checking\<close>
            | Some _ \<Rightarrow> None \<comment> \<open>the process doesn't have the trace, continue\<close>
          else
            None)
        (natural_of_nat breadth) of
          Some _ \<Rightarrow> None \<comment> \<open>we have the trace, but we are at the end\<close>
        | None \<Rightarrow> Some (to_check, has_tick))" 
| "cyphyaction_has_visible_trace_incremental_insts step_limit breadth ts P pred (e#t) has_tick s to_check =
    (case full_exhaustive_class.full_exhaustive
        (\<lambda> (a, term).
          if pred a then
            case cyphyaction_has_visible_trace_incremental step_limit ts (P a) (to_check @ [e] ) has_tick s of
              None \<Rightarrow> Some (True, []) \<comment> \<open>the process has the trace, stop checking\<close>
            | Some _ \<Rightarrow> None \<comment> \<open>the process doesn't have the trace, continue\<close>
          else
            None)
        (natural_of_nat breadth) of
          Some _ \<Rightarrow> \<comment> \<open>we have the trace, try the next event\<close>
            cyphyaction_has_visible_trace_incremental_insts step_limit breadth ts P pred t has_tick s (to_check @ [e] )
        | None \<Rightarrow> Some (to_check, False))"

section \<open>Performing refinement checking using trace checking\<close>

fun try_product :: "('a \<Rightarrow> 'b \<Rightarrow> 'c option) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c option" where
  "try_product f [] ys = None"
| "try_product f xs [] = None"
| "try_product f (x#xs) (y#ys) =
    (case f x y of
      Some r \<Rightarrow> Some r
    | None \<Rightarrow> 
        (case try_product f xs (y#ys) of 
          Some r \<Rightarrow> Some r
        | None \<Rightarrow> try_product f (x#xs) (ys)))"

fun cyphycircus_trace_incremental_ref_by_no_hiding
      :: "nat \<Rightarrow> real \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool \<Rightarrow> ('e::full_exhaustive, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (bool \<times> term list) option" where
  "cyphycircus_trace_incremental_ref_by_no_hiding step_limit ts s1 s2 has_tick P Q breadth (n::nat) =
    (if n = 0 then
      None
    else
      \<comment> \<open>try a visible event on both sides\<close>
      (full_exhaustive_class.full_exhaustive 
        (\<lambda> (e,term).
          (case (cyphyaction_check_trace step_limit ts has_tick  (s1, [Visible e], Some P),
                cyphyaction_check_trace step_limit ts has_tick (s2, [Visible e], Some Q)) of
              (Some [], Some []) \<Rightarrow> \<comment> \<open>both failed, can't get a counterexample from this\<close>
                None
            | (Some [], Some (y#ys)) \<Rightarrow> \<comment> \<open>counterexample found\<close>
                Some (False, [term ()] )
            | (Some (x#xs), Some []) \<Rightarrow> \<comment> \<open>Q failed but P succeeded, this is allowed so no counterexample\<close>
                None
            | (Some (x#xs), Some (y#ys)) \<Rightarrow> \<comment> \<open>try all the combinations of continuations to see if we can find a counterexample\<close>
                try_product 
                  (\<lambda> p q. case (p, q) of
                    ((s1', Some P'), (s2', Some Q')) \<Rightarrow> \<comment> \<open>continue to see if there is a trace P might fail on\<close>
                        (case cyphycircus_trace_incremental_ref_by_no_hiding step_limit ts s1' s2' has_tick P' Q' breadth (n-1) of 
                          Some (success, term_trace) => Some (success, term () # term_trace)
                        | _ \<Rightarrow> None))
                    (x#xs) (y#ys)
            | _ \<Rightarrow> None))
                 (natural_of_nat breadth)))
          "

section \<open>Running checks from ML\<close>

ML \<open>fun contains_hiding_name t = Term.exists_Const (fn (c, _) => c = @{const_name cHide}) t\<close>

ML \<open>
structure Trace_Evaluation = Proof_Data
(
  type T = unit -> term list option
  val empty: T = fn () => raise Fail "Trace_Evaluation"
  fun init _ = empty
);
val trace_eval_cookie = (Trace_Evaluation.get, Trace_Evaluation.put, "Trace_Evaluation.put");
\<close>

definition [code]: "code_real_of_rat n k \<equiv> Ratreal (rat_of_rational (Frct_integer (integer_of_nat n, integer_of_nat k)))"
definition [code]: "code_real_inv k \<equiv> Ratreal (rat_of_rational (Frct_integer (1, integer_of_nat k)))"
definition [code]: "unpack_trace_check_result \<equiv> map_option (map term_of_class.term_of o snd)"

ML \<open>fun check_cyphycircus_trace_incremental_ref_by_no_hiding ctxt stT evT breadth depth step_limit timestep_term has_tick spec impl = 
  let val actT = Type (@{type_name cyphyaction}, [evT, stT])
      val resT = Type (@{type_name option}, [HOLogic.mk_prodT (HOLogic.boolT, HOLogic.listT HOLogic.termT)])
      val cyphycircus_trace_incremental_ref_by = Const (@{const_name cyphycircus_trace_incremental_ref_by_no_hiding},
                HOLogic.natT --> HOLogic.realT --> stT --> stT --> HOLogic.boolT
                  --> actT --> actT --> HOLogic.natT --> HOLogic.natT --> resT)
      val unpack_result = @{term "map_option snd :: (bool \<times> term list) option \<Rightarrow> term list option"}
      val term = cyphycircus_trace_incremental_ref_by
                  $ (HOLogic.mk_nat step_limit)
                  $ timestep_term
                  $ (Const (@{const_name default}, stT)) (* initial state for P *)
                  $ (Const (@{const_name default}, stT)) (* initial state for Q *)
                  $ (if has_tick then @{term True} else @{term False})
                  $ spec
                  $ impl
                  $ (HOLogic.mk_nat breadth)
                  $ (HOLogic.mk_nat depth)
  in
    if contains_hiding_name spec orelse contains_hiding_name impl then
      Exn.Exn (TERM ("Specification or implementation contains hiding", 
        [Const (@{const_name HOL.eq}, dummyT) $ Free ("specification", dummyT) $ spec, 
         Const (@{const_name HOL.eq}, dummyT) $ Free ("implementation", dummyT) $ impl]))
    else
      Code_Runtime.dynamic_value_exn trace_eval_cookie ctxt NONE (Option.map o map) (unpack_result $ term) []
  end\<close>


term cyphyaction_has_visible_trace_incremental_insts
term "map_option (map term_of_class.term_of o snd)"
ML \<open>@{term "map_option (map term_of_class.term_of o snd)"}\<close>
ML \<open>fun check_cyphycircus_has_trace_incremental_insts ctxt stT evT breadth step_limit timestep_term trace has_tick P P_pred = 
  let val specT = fastype_of P
      val predT = fastype_of P_pred
      val resT = Type (@{type_name option}, [HOLogic.mk_prodT (HOLogic.listT evT, HOLogic.boolT)])
      val cyphycircus_has_trace_incremental = Const (@{const_name cyphyaction_has_visible_trace_incremental_insts},
                HOLogic.natT --> HOLogic.natT --> HOLogic.realT --> specT --> predT --> (HOLogic.listT evT) --> HOLogic.boolT --> stT
                  --> (HOLogic.listT evT) --> resT)
      val unpack_result =  Const (@{const_name unpack_trace_check_result}, resT --> Type (@{type_name option}, [HOLogic.listT HOLogic.termT]))
      val term = cyphycircus_has_trace_incremental
                  $ (HOLogic.mk_nat step_limit)
                  $ (HOLogic.mk_nat breadth)
                  $ timestep_term
                  $ P
                  $ P_pred
                  $ (HOLogic.mk_list evT trace)
                  $ (if has_tick then @{term True} else @{term False})
                  $ (Const (@{const_name default}, stT)) (* initial state *)
                  $ (HOLogic.mk_list evT [])
  in if contains_hiding_name P then
      Exn.Exn (TERM ("Specification contains hiding", 
        [Const (@{const_name HOL.eq}, dummyT) $ Free ("specification", dummyT) $ P]))
    else
      Code_Runtime.dynamic_value_exn trace_eval_cookie ctxt NONE (Option.map o map) (unpack_result $ term) []
  end\<close>

section \<open>testing the codegen\<close>


chantype foo =
  a :: nat                                    
  b :: unit

alphabet bar =
  n :: nat
  v :: real
  time :: real

record_default bar

abbreviation "test_events \<equiv> [b_C (), a_C 0, a_C 1, a_C 2, a_C 3, a_C 4]"
abbreviation "test_traces \<equiv> b_lists 4 test_events"
abbreviation "visibility_test_events \<equiv> map Visible test_events @ map (Hidden 0) test_events @ map (Hidden 1) test_events"
abbreviation "test_visibility_traces \<equiv> b_lists 4 visibility_test_events"
abbreviation "traces_of P \<equiv>
  map (\<lambda>t. (t, False))
    (filter (\<lambda>t. Option.is_none (cyphyaction_has_visible_trace_incremental 1000 (code_real_inv 100) P t False (default::bar))) test_traces)
  @ map (\<lambda>t. (t, True))
    (filter (\<lambda>t. Option.is_none (cyphyaction_has_visible_trace_incremental 1000 (code_real_inv 100) P t True (default::bar))) test_traces)"
abbreviation "visibility_traces_of P \<equiv>
  map (\<lambda>t. (t, False))
    (filter (\<lambda>t. Option.is_none (cyphyaction_has_trace_incremental 1000 (code_real_inv 100) P t False (default::bar))) test_visibility_traces)
  @ map (\<lambda>t. (t, True))
    (filter (\<lambda>t. Option.is_none (cyphyaction_has_trace_incremental 1000 (code_real_inv 100) P t True (default::bar))) test_visibility_traces)"

subsection \<open>Test 1: @{term "a\<^bold>.1 \<rightarrow> a\<^bold>!2 \<rightarrow> Skip \<sqsubseteq> a\<^bold>.1 \<rightarrow> a\<^bold>!0 \<rightarrow> Skip"} gives @{term "[a_C 1, a_C 0]"}\<close>

ML \<open>let val term_string = Pretty.pure_string_of o Syntax.pretty_term @{context}
        fun traceToString trace = String.concatWith " \<rightarrow> " (map term_string trace)
    in  Option.map traceToString (Exn.release (check_cyphycircus_trace_incremental_ref_by_no_hiding @{context} @{typ bar} @{typ foo} 10 10 1000 @{term "code_real_inv 100"} false
      @{term "a\<^bold>.1 \<rightarrow> a\<^bold>!2 \<rightarrow> Skip :: (foo, bar) cyphyaction"}
      @{term "a\<^bold>.1 \<rightarrow> a\<^bold>!0 \<rightarrow> Skip :: (foo, bar) cyphyaction"}))
    end\<close>

value "traces_of (a\<^bold>.1 \<rightarrow> a\<^bold>!2 \<rightarrow> Skip)"
value "traces_of (a\<^bold>.1 \<rightarrow> a\<^bold>!0 \<rightarrow> Skip)"

subsection \<open>Test 2: @{term "a\<^bold>.1 \<rightarrow> a\<^bold>!0 \<rightarrow>  Skip \<sqsubseteq> a\<^bold>.1 \<rightarrow> a\<^bold>?x \<rightarrow> Skip"} gives @{term "[a_C 1, a_C 1]"}\<close>

ML \<open>let val term_string = Pretty.pure_string_of o Syntax.pretty_term @{context}
        fun traceToString trace = String.concatWith " \<rightarrow> " (map term_string trace)
    in  Option.map traceToString (Exn.release (check_cyphycircus_trace_incremental_ref_by_no_hiding @{context} @{typ bar} @{typ foo} 10 10 1000 @{term "code_real_inv 100"} false
      @{term "a\<^bold>.1 \<rightarrow> a\<^bold>!0 \<rightarrow> Skip :: (foo, bar) cyphyaction"}
      @{term "a\<^bold>.1 \<rightarrow> a\<^bold>?x \<rightarrow> Skip :: (foo, bar) cyphyaction"}))
    end\<close>

value "traces_of (a\<^bold>.1 \<rightarrow> a\<^bold>!0 \<rightarrow> Skip)"
value "traces_of (a\<^bold>.1 \<rightarrow> a\<^bold>?x \<rightarrow> Skip)"

subsection \<open>Test 3: @{term "b \<rightarrow> Skip \<sqsubseteq> (\<mu> X. b \<rightarrow> X)"} gives @{term "[b_C (), b_C ()]"}\<close>

recursive where "baz = b \<rightarrow> baz"

ML \<open>let val term_string = Pretty.pure_string_of o Syntax.pretty_term @{context}
        fun traceToString trace = String.concatWith " \<rightarrow> " (map term_string trace)
    in  Option.map traceToString (Exn.release (check_cyphycircus_trace_incremental_ref_by_no_hiding @{context} @{typ bar} @{typ foo} 10 10 1000 @{term "code_real_inv 100"} false
       @{term "b \<rightarrow> Skip :: (foo, bar) cyphyaction"}
      (Raw_Simplifier.rewrite_term @{theory} @{thms recursive_defs rec_sys_defs cyphyaction_datatype_unfolds} [] @{term "baz :: (foo, bar) cyphyaction"})))
    end\<close>

value "traces_of (b \<rightarrow> Skip)"
value "traces_of (baz)"

subsection \<open>Test 4: @{term "(\<mu> X. b \<rightarrow> X) \<sqsubseteq> b \<rightarrow> Skip"} gives @{term "[b_C ()]"} with tick}\<close>

ML \<open>let val term_string = Pretty.pure_string_of o Syntax.pretty_term @{context}
        fun traceToString trace = String.concatWith " \<rightarrow> " (map term_string trace)
    in  Option.map traceToString (Exn.release (check_cyphycircus_trace_incremental_ref_by_no_hiding @{context} @{typ bar} @{typ foo} 10 10 1000 @{term "code_real_inv 100"} true
      (Raw_Simplifier.rewrite_term @{theory} @{thms recursive_defs rec_sys_defs cyphyaction_datatype_unfolds} [] @{term "baz :: (foo, bar) cyphyaction"})
      @{term "b \<rightarrow> Skip :: (foo, bar) cyphyaction"}))
    end\<close>

subsection \<open>Test 5: Continuous Evolution test, expect trace @{term "[a_C 2, a_C 4, a_C 6]"} etc.}\<close>

recursive where
  "test5_cont =
    (cEvolve (v +\<^sub>L time) (\<lambda>_. \<lparr>n\<^sub>v=0, v\<^sub>v=2, time\<^sub>v=1\<rparr>) (time < 1)\<^sub>e) ;; time := 0 ;;
    a\<^bold>!(nat (floor v)) \<rightarrow> test5_cont"
recursive where
  "test5_discr = n := n+2 ;; a\<^bold>!n \<rightarrow> test5_discr"

text \<open>Refinement @{term "test5_cont \<sqsubseteq> a\<^bold>!2 \<rightarrow> a\<^bold>!0 \<rightarrow>  Skip"}, gives @{term "[a_C 2, a_C 0]"}\<close>
ML \<open>let val term_string = Pretty.pure_string_of o Syntax.pretty_term @{context}
        fun traceToString trace = String.concatWith " \<rightarrow> " (map term_string trace)
    in  Option.map traceToString (Exn.release (check_cyphycircus_trace_incremental_ref_by_no_hiding @{context} @{typ bar} @{typ foo} 10 10 1000 @{term "code_real_inv 100"} false
      (@{term "test5_cont :: (foo, bar) cyphyaction"})
      @{term "a\<^bold>!2 \<rightarrow> a\<^bold>!0 \<rightarrow>  Skip :: (foo, bar) cyphyaction"}))
    end\<close>

value "traces_of test5_cont"
value "traces_of test5_discr"
value "cyphyaction_has_visible_trace_incremental 1000 (code_real_inv 100) test5_cont [a_C 2, a_C 4, a_C 6, a_C 8, a_C 10] False (default::bar)"
value "cyphyaction_has_visible_trace_incremental 1000 (code_real_inv 100) test5_cont [a_C 2, a_C 4, a_C 6, a_C 8, a_C 10] True (default::bar)"
value "cyphyaction_has_visible_trace_incremental 1000 (code_real_inv 100) test5_cont [a_C 2, a_C 4, a_C 6, a_C 8, a_C 0] False (default::bar)"


subsection \<open>Test 6: Parallelism and hiding test\<close>

text \<open>Refinement @{term "((a\<^bold>.0 \<rightarrow> b \<rightarrow> Skip) \<lbrakk>\<^bold>0|\<lbrace>b\<rbrace>|\<^bold>0\<rbrakk> (b \<rightarrow> a\<^bold>.1 \<rightarrow> Skip)) \<Zhide> \<lbrace>b\<rbrace> \<sqsubseteq> a\<^bold>!0 \<rightarrow> b \<rightarrow> a\<^bold>!1 \<rightarrow>  Skip"}
      gives @{term "[a_C 0, b_C ()]"}. This ensures hidden events are, in fact, hidden.\<close>

(* errors out on refinement check due to hiding *)
ML \<open>case (check_cyphycircus_trace_incremental_ref_by_no_hiding @{context} @{typ bar} @{typ foo} 10 10 1000 @{term "code_real_inv 100"} false
      (@{term "((a\<^bold>.0 \<rightarrow> b \<rightarrow> Skip) \<lbrakk>\<^bold>0|\<lbrace>b\<rbrace>|\<^bold>0\<rbrakk> (b \<rightarrow> a\<^bold>.1 \<rightarrow> Skip)) \<Zhide> \<lbrace>b\<rbrace> :: (foo, bar) cyphyaction"})
      @{term "a\<^bold>!0 \<rightarrow> b \<rightarrow> a\<^bold>!1 \<rightarrow>  Skip :: (foo, bar) cyphyaction"}) of
        Exn.Res _ => error "Expected exception to be thrown"
      | Exn.Exn e => if Exn.is_interrupt e then Exn.reraise e else (writeln o Runtime.exn_message o (Runtime.exn_context (SOME @{context}))) e\<close> 
ML \<open>case (check_cyphycircus_trace_incremental_ref_by_no_hiding @{context} @{typ bar} @{typ foo} 10 10 1000 @{term "code_real_inv 100"} false
      @{term "a\<^bold>!0 \<rightarrow> a\<^bold>!1 \<rightarrow>  Skip :: (foo, bar) cyphyaction"}
      (@{term "((a\<^bold>.0 \<rightarrow> b \<rightarrow> Skip) \<lbrakk>\<^bold>0|\<lbrace>b\<rbrace>|\<^bold>0\<rbrakk> (b \<rightarrow> a\<^bold>.1 \<rightarrow> Skip)) \<Zhide> \<lbrace>b\<rbrace> :: (foo, bar) cyphyaction"})) of
        Exn.Res _ => error "Expected exception to be thrown"
      | Exn.Exn e => if Exn.is_interrupt e then Exn.reraise e else (writeln o Runtime.exn_message o (Runtime.exn_context (SOME @{context}))) e\<close>

value "visibility_traces_of (((a\<^bold>.0 \<rightarrow> b \<rightarrow> Skip) \<lbrakk>\<^bold>0|\<lbrace>b\<rbrace>|\<^bold>0\<rbrakk> (b \<rightarrow> a\<^bold>.1 \<rightarrow> Skip)) \<Zhide> \<lbrace>b\<rbrace>)"
value "visibility_traces_of (a\<^bold>!0 \<rightarrow> a\<^bold>!1 \<rightarrow>  Skip)"
value "remdups
      (map (apfst (List.map_filter (case_visibility Some (\<lambda>_ _. None))))
        (visibility_traces_of (((a\<^bold>.0 \<rightarrow> b \<rightarrow> Skip) \<lbrakk>\<^bold>0|\<lbrace>b\<rbrace>|\<^bold>0\<rbrakk> (b \<rightarrow> a\<^bold>.1 \<rightarrow> Skip)) \<Zhide> \<lbrace>b\<rbrace>)))"
value "remdups
      (map (apfst (List.map_filter (case_visibility Some (\<lambda>_ _. None))))
        (visibility_traces_of (a\<^bold>!0 \<rightarrow> a\<^bold>!1 \<rightarrow>  Skip)))"

subsection \<open>Test 7: Mutual recursion test\<close>

recursive test7 :: "(foo, bar) cyphyaction"
      and test7_2 :: "(foo, bar) cyphyaction"
      and test7_3 :: "(foo, bar) cyphyaction" where
  "(test7 :: (foo, bar) cyphyaction) = a\<^bold>.0 \<rightarrow> test7_2"
| "(test7_2 :: (foo, bar) cyphyaction) = a\<^bold>.1 \<rightarrow> test7_3"
| "(test7_3 :: (foo, bar) cyphyaction) = a\<^bold>.2 \<rightarrow> test7"

text \<open>Refinement @{term "test7  \<sqsubseteq> a\<^bold>!0 \<rightarrow> a\<^bold>!1 \<rightarrow> b \<rightarrow>  Skip"} gives @{term "[a_C 0, a_C 1, b_C ()]"}\<close>
ML \<open>let val term_string = Pretty.pure_string_of o Syntax.pretty_term @{context}
        fun traceToString trace = String.concatWith " \<rightarrow> " (map term_string trace)
    in Option.map traceToString (Exn.release (check_cyphycircus_trace_incremental_ref_by_no_hiding @{context} @{typ bar} @{typ foo} 10 10 1000 @{term "code_real_inv 100"} false
      (Raw_Simplifier.rewrite_term @{theory} @{thms recursive_defs rec_sys_defs cyphyaction_datatype_unfolds} [] @{term "test7 :: (foo, bar) cyphyaction"})
      @{term "a\<^bold>!0 \<rightarrow> a\<^bold>!1 \<rightarrow> b \<rightarrow>  Skip :: (foo, bar) cyphyaction"}))
    end\<close>

value "traces_of test7"

subsection \<open>Test 8: refinement @{term "a\<^bold>!0 \<rightarrow> (inf (a\<^bold>!1 \<rightarrow>  Skip) (a\<^bold>!2 \<rightarrow>  Skip)) \<sqsubseteq> a\<^bold>!0 \<rightarrow> a\<^bold>!1 \<rightarrow>  Skip"} holds\<close>

ML \<open>let val term_string = Pretty.pure_string_of o Syntax.pretty_term @{context}
        fun traceToString trace = String.concatWith " \<rightarrow> " (map term_string trace)
    in Option.map traceToString (Exn.release (check_cyphycircus_trace_incremental_ref_by_no_hiding @{context} @{typ bar} @{typ foo} 10 10 1000 @{term "code_real_inv 100"} false
      @{term "a\<^bold>!0 \<rightarrow> (inf (a\<^bold>!1 \<rightarrow>  Skip) (a\<^bold>!2 \<rightarrow>  Skip)) :: (foo, bar) cyphyaction"}
      @{term "a\<^bold>!0 \<rightarrow> a\<^bold>!1 \<rightarrow>  Skip :: (foo, bar) cyphyaction"}))
    end\<close>

value "traces_of (a\<^bold>!0 \<rightarrow> (inf (a\<^bold>!1 \<rightarrow>  Skip) (a\<^bold>!2 \<rightarrow>  Skip)))"

subsection \<open>Test 9: refinement @{term "a\<^bold>!0 \<rightarrow> a\<^bold>!1 \<rightarrow>  Skip \<sqsubseteq> a\<^bold>!0 \<rightarrow> (inf (a\<^bold>!1 \<rightarrow>  Skip) (a\<^bold>!2 \<rightarrow>  Skip))"} gives @{term "[a_C 0, a_C 2]"}\<close>

ML \<open>let val term_string = Pretty.pure_string_of o Syntax.pretty_term @{context}
        fun traceToString trace = String.concatWith " \<rightarrow> " (map term_string trace)
    in Option.map traceToString (Exn.release (check_cyphycircus_trace_incremental_ref_by_no_hiding @{context} @{typ bar} @{typ foo} 10 10 1000 @{term "code_real_inv 100"} false
      @{term "a\<^bold>!0 \<rightarrow> a\<^bold>!1 \<rightarrow>  Skip :: (foo, bar) cyphyaction"}      
      @{term "a\<^bold>!0 \<rightarrow> (inf (a\<^bold>!1 \<rightarrow>  Skip) (a\<^bold>!2 \<rightarrow>  Skip)) :: (foo, bar) cyphyaction"}))
    end\<close>

hide_type foo bar

hide_const n v time a b

end
