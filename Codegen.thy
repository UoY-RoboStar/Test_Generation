theory Codegen
  imports Axiomatic_CyPhyCircus.Ax_CyPhyCircus
    "ITree_Simulation.Code_Target_Rational" Interaction_Trees.ITree_Extraction
    "HOL-Library.Multiset" "Framed_ODEs.Framed_ODEs" (*"HOL-Library.Code_Real_Approx_By_Float"*)
begin

unbundle Circus_Syntax
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

axiomatization
  cEvolve' :: "(real \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('e, 's) cyphyaction" and
  cInputPrefix' :: "('e \<Rightarrow> (('s \<Rightarrow> \<bool>) \<times> ('e, 's) cyphyaction) option) \<Rightarrow> ('e, 's) cyphyaction" and
  cOutputPrefix' :: "('s \<Rightarrow> 'e) \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction" and
  cParallelAct' :: "('s \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> 'e set \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction" and
  cRec' :: "(nat \<Rightarrow> ('e, 's) cyphyaction) \<Rightarrow> ('e, 's) cyphyaction"
where
  cEvolve_cEvolve'[code_unfold]:
    "cEvolve v f p \<equiv> cEvolve' (\<lambda>r s. put\<^bsub>v\<^esub> s (RKstep (\<lambda>x. get\<^bsub>v\<^esub> (f (put\<^bsub>v\<^esub> s x))) r (get\<^bsub>v\<^esub> s))) p" and
  cInputPrefix_cInputPrefix'[code_unfold]:
    "cInputPrefix c S F \<equiv> cInputPrefix' (\<lambda>e.  map_option F ((match\<^bsub>c\<^esub> e) \<bind> (map_id_on S)))" and
  cOutputPrefix_cOutputPrefix'[code_unfold]:
    "cOutputPrefix c expr P \<equiv> cOutputPrefix' (build\<^bsub>c\<^esub> \<circ> expr) P" and
  cParallelAct_cParallelAct'[code_unfold]:
    "cParallelAct ns1 ns2 cs P Q \<equiv> cParallelAct' (\<lambda> s0 s1 s2. s0 \<triangleleft>\<^bsub>ns1\<^esub> s1 \<triangleleft>\<^bsub>ns2\<^esub> s2) cs P Q" and
  nu_cRec'[code_unfold]:
    "\<nu> FF \<equiv> cRec' (\<lambda>n. Nat.funpow n FF cChaos)"
for v :: "'b :: real_normed_vector \<Longrightarrow> 's"
and f :: "'s \<Rightarrow> 's"
and p :: "'s \<Rightarrow> bool"

lemmas cyphyaction_datatype_unfolds =
  cEvolve_cEvolve' cInputPrefix_cInputPrefix' cOutputPrefix_cOutputPrefix' cParallelAct_cParallelAct' nu_cRec'

code_datatype cSkip cAssigns cStop cChaos cAssume cEvolve' cSyncPrefix cOutputPrefix' cInputPrefix'
  cSeq cGuard cCond "inf :: ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction"
  cExtChoice cParallelAct' cRec'

section \<open>Operational semantics for trace checking\<close>

datatype ('e, 's) cyphystep =
  Termination 's
  | Timestep 's bool "('e, 's) cyphyaction"
  | StUpd 's "('e, 's) cyphyaction"
  | EventStep  'e "'e list" "('e, 's) cyphyaction"

axiomatization
  step_cyphyaction :: "real \<Rightarrow> 'e list \<Rightarrow> 's \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphystep list option"
  where
  step_cyphyaction_cAssigns[code]: (* terminate immediately with updated state *)
    "step_cyphyaction timestep t s (cAssigns subst) = Some [Termination (subst s)]" and
  step_cyphyaction_cStop[code]: (* deadlock without terminating *)
    "step_cyphyaction timestep t s cStop = Some []" and
  step_cyphyaction_cChaos[code]: (* error out of checking *)
    "step_cyphyaction timestep t s cChaos = None" and
  step_cyphyaction_cAssume[code]: (* error out of checking if condition is false, terminate if true *)
    "step_cyphyaction timestep t s (cAssume pred)
      = (if pred s then Some [Termination s] else None)" and
  step_cyphyaction_cEvolve'[code]: (* terminate immediately if condition false, otherwise update according to solution and time passes *)
    "step_cyphyaction timestep t s (cEvolve' sol pred)
      = Some (if pred s then [Timestep (sol timestep s) True (cEvolve' sol pred)] else [Termination s] )" and
  step_cyphyaction_cSyncPrefix1[code]: (* no event means checking fails *)
    "step_cyphyaction timestep [] s (cSyncPrefix e P) = None" and
  step_cyphyaction_cSyncPrefix2[code]: (* check if event is correct, also allow time to pass if event is correct *)
    "step_cyphyaction timestep (te#t) s (cSyncPrefix e P)
      = (if te = build\<^bsub>e\<^esub> () then Some [EventStep te t P, Timestep s False (cSyncPrefix e P)] else Some [])" and
  step_cyphyaction_cOutputPrefix'1[code]: (* no event means checking fails *)
    "step_cyphyaction timestep [] s (cOutputPrefix' chexpr P) = None" and
  step_cyphyaction_cOutputPrefix'2[code]: (* check if event is correct, also allow time to pass if event is correct *)
    "step_cyphyaction timestep (te#t) s (cOutputPrefix' chexpr P)
      = (if chexpr s = te then Some [EventStep te t P, Timestep s False (cOutputPrefix' chexpr P)] else Some [])" and
  step_cyphyaction_cInputPrefix'1[code]: (* no event means checking fails *)
    "step_cyphyaction timestep [] s (cInputPrefix' F) = None" and
  step_cyphyaction_cInputPrefix'2[code]: (* check if event is correct, also allow time to pass if event is correct *)
    "step_cyphyaction timestep (te#t) s (cInputPrefix' F)
      = (case F te of
          None \<Rightarrow> Some [] \<comment> \<open>event not valid, deadlock\<close>
        | Some (pred, P) \<Rightarrow> \<comment> \<open>event is valid, but is the predicate true?\<close>
            if pred s then
              Some [EventStep te t P, Timestep s False (cInputPrefix' F)]
            else
              Some [Timestep s False (cInputPrefix' F)] \<comment> \<open> we can wait until the predicate is true \<close> )" and
  step_cyphyaction_cSeq[code]: (* try the first, then proceed to the second after termination *)
    "step_cyphyaction timestep t s (cSeq P Q) =
      (case (step_cyphyaction timestep t s P) of
          Some xs \<Rightarrow>
            Some (map
              (\<lambda> step. case step of
                  Termination s' \<Rightarrow> StUpd s' Q
                | Timestep s' strict P' \<Rightarrow> Timestep s' strict (cSeq P' Q)
                | StUpd s' P' \<Rightarrow> StUpd s' (cSeq P' Q)
                | EventStep te t' P' \<Rightarrow> EventStep te t' (cSeq P' Q))
              xs)
        | None \<Rightarrow> None)" and
  step_cyphyaction_cGuard[code]: (* deadlock if predicate is false, otherwise behave as inner action*)
    "step_cyphyaction timestep t s (cGuard pred P)
      = (if pred s then step_cyphyaction timestep t s P else Some [])" and
  step_cyphyaction_cCond[code]: (* behave as either inner action depending on predicate*)
    "step_cyphyaction timestep t s (cCond P pred Q)
      = (if pred s then step_cyphyaction timestep t s P else step_cyphyaction timestep t s Q)" and
  step_cyphyaction_inf[code]: (* evaluate both and concatenate results *)
    "step_cyphyaction timestep t s (inf P Q)
      = (case (step_cyphyaction timestep t s P, step_cyphyaction timestep t s Q) of
          (Some xs, Some ys) \<Rightarrow> Some (xs @ ys)
        | (None, Some ys) \<Rightarrow> Some ys
        | (Some xs, None) \<Rightarrow> Some xs
        | (None, None) \<Rightarrow> None)" and
  step_cyphyaction_cExtChoice[code]: (* synchronise timesteps, concatenate choices *)
    "step_cyphyaction timestep t s (cExtChoice P Q)
      = (case (step_cyphyaction timestep t s P, step_cyphyaction timestep t s Q) of
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
        | (None, Some ys) \<Rightarrow> Some ys
        | (Some xs, None) \<Rightarrow> Some xs
        | (None, None) \<Rightarrow> None)" and
  step_cyphyaction_cParallelAct'[code]: (* synchronise timesteps, events in syncset, and termination *)
    "step_cyphyaction timestep t s (cParallelAct' mrg cs P Q)
      = (let is_timestep = (\<lambda> step. case step of Timestep _ _ _ \<Rightarrow> True | _ \<Rightarrow> False);
            is_sync_event = (\<lambda> step. case step of EventStep e _ _ \<Rightarrow> e \<in> cs | _ \<Rightarrow> False);
            is_termination = (\<lambda> step. case step of Termination _ \<Rightarrow> True | _ \<Rightarrow> False)
        in case (step_cyphyaction timestep t s P, step_cyphyaction timestep t s Q) of
              (Some xs, Some ys) \<Rightarrow>
            (case (List.partition is_timestep xs, List.partition is_timestep ys) of
              ((xs_ts, xs), (ys_ts, ys)) \<Rightarrow>
                case (List.partition is_sync_event xs, List.partition is_sync_event ys) of
                  ((xs_syncs, xs), (ys_syncs, ys)) \<Rightarrow>
                    case (List.partition is_termination xs, List.partition is_termination ys) of
                      ((xs_terms, xs), (ys_terms, ys)) \<Rightarrow>
                        Some (
                          \<comment> \<open>unsynchronised steps evolve one side, merging the state\<close>
                          (map (\<lambda> step. case step of
                                EventStep e t P' \<Rightarrow> EventStep e t (cParallelAct' mrg cs P' Q)
                              | StUpd s' P' \<Rightarrow> StUpd (mrg s s' s) (cParallelAct' mrg cs P' Q))
                            xs)
                          @ (map (\<lambda> step. case step of
                                EventStep e t Q' \<Rightarrow> EventStep e t (cParallelAct' mrg cs P Q')
                              | StUpd s' Q' \<Rightarrow> StUpd (mrg s s s') (cParallelAct' mrg cs P Q'))
                            ys)
                          \<comment> \<open>timesteps are synchronised, merging the state\<close>
                          @ (map (\<lambda>(x, y). case (x, y) of
                                (Timestep s1 strict1 P', Timestep s2 strict2 Q') \<Rightarrow>
                                  Timestep (mrg s s1 s2) (disj strict1 strict2) (cParallelAct' mrg cs P' Q'))
                              (List.product xs_ts ys_ts))
                          \<comment> \<open>events in the synchronisation set are synchronised, there is no state update\<close>
                          @ (List.bind (List.product xs_syncs ys_syncs)
                              (\<lambda>(x, y). case (x, y) of
                                  (EventStep e1 t1 P', EventStep e2 t2 Q') \<Rightarrow>
                                    if e1 = e2 then 
                                      [EventStep e1 t1 (cParallelAct' mrg cs P' Q')]
                                    else
                                      [])
                              ) 
                          \<comment> \<open>terminations are synchronised, merging the state\<close>
                          @ (map (\<lambda>(x, y). case (x, y) of
                                (Termination s1, Termination s2) \<Rightarrow>
                                  Termination (mrg s s1 s2))
                              (List.product xs_terms ys_terms))
                          ))
            | _ \<Rightarrow> None \<comment> \<open>if either side errors out, the whole thing does\<close>)" and
  step_cyphyaction_cRec'[code]: (* unroll the loop at least enough to match the trace *)
    "step_cyphyaction timestep t s (cRec' FF)
      = step_cyphyaction timestep t s (FF (1 + length t))"

lemma step_cyphyaction_cSkip[code]:
    "step_cyphyaction timestep t s cSkip = Some [Termination s]"
  unfolding cSkip_def step_cyphyaction_cAssigns by simp

fun cyphyaction_has_trace :: "nat \<Rightarrow> real \<Rightarrow> 'e list \<Rightarrow> bool \<Rightarrow> 's \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('s \<times> ('e, 's) cyphyaction option) option option" and
    check_cyphysteps :: "('e, 's) cyphyaction \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> 'e list \<Rightarrow> bool \<Rightarrow> 's \<Rightarrow> ('s \<times> ('e, 's) cyphyaction option) option option \<Rightarrow> ('e, 's) cyphystep list \<Rightarrow> ('s \<times> ('e, 's) cyphyaction option) option option" where
  "cyphyaction_has_trace limit ts t has_tick s P = 
    (if limit = 0 then
      None
    else
      case (t, has_tick) of
        ([], False) \<Rightarrow> Some (Some (s, Some P))
      | ([], True) \<Rightarrow> (step_cyphyaction ts [] s P) \<bind> 
        (\<lambda> steps. if List.null steps then Some None else  check_cyphysteps P (limit-1) ts [] True s None steps)
      | ((e#t), has_tick) \<Rightarrow> (step_cyphyaction ts (e#t) s P) \<bind>
        (\<lambda>steps. if List.null steps then Some None else check_cyphysteps P (limit-1) ts (e#t) has_tick s None steps))"
| "check_cyphysteps P limit ts t has_tick s r [] = r"
  (* every process has the empty trace *)
| "check_cyphysteps P limit ts [] False s r steps = Some (Some (s, Some P))"
  (* a process has a tick if it has some termination step *)
| "check_cyphysteps P limit ts [] True s r (Termination s' # steps) = Some (Some (s', None))"
  (* a process has a tick if it has a tick after a state update *)
| "check_cyphysteps P limit ts [] True s r (StUpd s' P' # steps) =
    (case cyphyaction_has_trace limit ts [] True s' P' of
      Some (Some (s', P')) \<Rightarrow> Some (Some (s', P'))
    | Some None \<Rightarrow> check_cyphysteps P limit ts [] True s (Some None) steps
    | None \<Rightarrow> check_cyphysteps P limit ts [] True s r steps)"
  (* a process has a tick if it has a tick after a (strict) timestep *)
| "check_cyphysteps P limit ts [] True s r (Timestep s' True P' # steps) =
    (case cyphyaction_has_trace limit ts [] True s' P' of
      Some (Some (s', P')) \<Rightarrow> Some (Some (s', P'))
    | Some None \<Rightarrow> check_cyphysteps P limit ts [] True s (Some None) steps
    | None \<Rightarrow> check_cyphysteps P limit ts [] True s r steps)"
  (* a non-strict timestep is ignored, but never propagates a None *)
| "check_cyphysteps P limit ts [] True s r (Timestep s' False P' # steps) =
    check_cyphysteps P limit ts [] True s (combine_options (combine_options (\<lambda> x y. y)) (Some None) r) steps"
  (* a process can't have just a tick when a event step happens *)
| "check_cyphysteps P limit ts [] True s r (EventStep e t' P' # steps) =
    check_cyphysteps P limit ts [] True s (Some None) steps"
  (* a process that can terminate doesn't necessarily have a non-empty trace *)
| "check_cyphysteps P limit ts (e#t) has_tick s r (Termination s' # steps) =
    check_cyphysteps P limit ts (e#t) has_tick s (Some None) steps"
  (* a process has a non-empty trace if it has it after a state update *)
| "check_cyphysteps P limit ts (e#t) has_tick s r (StUpd s' P' # steps) =
    (case cyphyaction_has_trace limit ts (e#t) has_tick s' P' of
      Some (Some (s', P')) \<Rightarrow> Some (Some (s', P'))
    | Some None \<Rightarrow> check_cyphysteps P limit ts (e#t) has_tick s (Some None) steps
    | None \<Rightarrow> check_cyphysteps P limit ts (e#t) has_tick s r steps)"
  (* a process has a non-empty trace if it has it after a (strict) timestep *)
| "check_cyphysteps P limit ts (e#t) has_tick s r (Timestep s' True P' # steps) =
    (case cyphyaction_has_trace limit ts (e#t) has_tick s' P' of
      Some (Some (s', P')) \<Rightarrow> Some (Some (s', P'))
    | Some None \<Rightarrow> check_cyphysteps P limit ts (e#t) has_tick s (Some None) steps
    | None \<Rightarrow> check_cyphysteps P limit ts (e#t) has_tick s r steps)"
  (* a non-strict timestep is ignored, but never propagates a none *)
| "check_cyphysteps P limit ts (e#t) has_tick s r (Timestep s' False P' # steps) =
    check_cyphysteps P limit ts (e#t) has_tick s (combine_options (combine_options (\<lambda> x y. y)) (Some None) r) steps"
  (* a process has a non-empty trace if it has the rest of it after an event *)
| "check_cyphysteps P limit ts (e#t) has_tick s r (EventStep e' t' P' # steps) =
    (case cyphyaction_has_trace limit ts t' has_tick s P' of
      Some (Some (s', P')) \<Rightarrow> Some (Some (s', P'))
    | Some None \<Rightarrow> check_cyphysteps P limit ts (e#t) has_tick s (Some None) steps
    | None \<Rightarrow> check_cyphysteps P limit ts (e#t) has_tick s r steps)"

fun filter_options :: "'a option list \<Rightarrow> 'a list" where
  "filter_options [] = []" |
  "filter_options (None # xs) = filter_options xs" |
  "filter_options (Some x # xs) = x # filter_options xs"

definition "cyphycircus_trace_ref_by step_limit ts s t has_tick P Q \<equiv>
  (case (cyphyaction_has_trace step_limit ts t has_tick s Q, cyphyaction_has_trace step_limit ts t has_tick s P) of
    (Some (Some _), Some (Some _)) \<Rightarrow> True
  | (Some (Some _), Some None) \<Rightarrow> False
  | (Some None, Some (Some _)) \<Rightarrow> True
  | (Some None, Some None) \<Rightarrow> True
  | _ \<Rightarrow> True)"

fun cyphycircus_trace_prefix_ref_by where
  "cyphycircus_trace_prefix_ref_by step_limit ts s t has_tick P Q term_limit (n::nat) =
    (if n = 0 then
      None
    else
          case full_exhaustive_class.full_exhaustive 
            (\<lambda> (e,term). case (cyphyaction_has_trace step_limit ts (t @ [e] ) has_tick s P, cyphyaction_has_trace step_limit ts (t @ [e] ) has_tick s Q) of
                (Some None, Some None) \<Rightarrow> None \<comment> \<open>no point continuing if the prefix fails\<close>
              | (Some None, Some (Some _)) \<Rightarrow> Some (has_tick, [term ()] ) \<comment> \<open>counterexample found\<close>
              | (Some (Some _), Some None) \<Rightarrow> None \<comment> \<open>Q is allowed to omit some traces of P, no point continuing if the prefix fails\<close>
              | (Some (Some _), Some (Some _)) \<Rightarrow> \<comment> \<open>continue to see if there is a trace P might fail on\<close>
                  (case cyphycircus_trace_prefix_ref_by step_limit ts s (t @ [e] ) has_tick P Q term_limit (n-1) of 
                    Some (_, term_trace) => Some (has_tick, (term ()) # term_trace)
                  | _ \<Rightarrow> None)
              | _ \<Rightarrow> None) (natural_of_nat term_limit) of 
                  Some (b, terms) \<Rightarrow> Some (b, terms)
                | None \<Rightarrow> None)"



fun cyphycircus_trace_incremental_ref_by where
  "cyphycircus_trace_incremental_ref_by step_limit ts s1 s2 has_tick P Q term_limit (n::nat) =
    (if n = 0 then
      None
    else
          case full_exhaustive_class.full_exhaustive 
            (\<lambda> (e,term). case (cyphyaction_has_trace step_limit ts [e] has_tick s1 P, cyphyaction_has_trace step_limit ts [e] has_tick s2 Q) of
                (Some None, Some None) \<Rightarrow> None \<comment> \<open>no point continuing if the prefix fails\<close>
              | (Some None, Some (Some _)) \<Rightarrow> Some (has_tick, [term ()] ) \<comment> \<open>counterexample found\<close>
              | (Some (Some _), Some None) \<Rightarrow> None \<comment> \<open>Q is allowed to omit some traces of P, no point continuing if the prefix fails\<close>
              | (Some (Some (s1', None)), Some (Some (s2', None))) \<Rightarrow> None
              | (Some (Some (s1', Some _)), Some (Some (s2', None))) \<Rightarrow> None
              | (Some (Some (s1', None)), Some (Some (s2', Some Q'))) \<Rightarrow> 
                  \<comment> \<open>P terminated but Q might do further events (yielding a counterexample), continue with Stop\<close>
                  (case cyphycircus_trace_incremental_ref_by step_limit ts s1' s2' has_tick cStop Q' term_limit (n-1) of 
                    Some (_, term_trace) => Some (has_tick, (term ()) # term_trace)
                  | _ \<Rightarrow> None)
              | (Some (Some (s1', Some P')), Some (Some (s2', Some Q'))) \<Rightarrow> \<comment> \<open>continue to see if there is a trace P might fail on\<close>
                  (case cyphycircus_trace_incremental_ref_by step_limit ts s1' s2' has_tick P' Q' term_limit (n-1) of 
                    Some (_, term_trace) => Some (has_tick, (term ()) # term_trace)
                  | _ \<Rightarrow> None)
              | _ \<Rightarrow> None) (natural_of_nat term_limit) of 
                  Some (b, terms) \<Rightarrow> Some (b, terms)
                | None \<Rightarrow> None)"

ML \<open>
structure Trace_Evaluation = Proof_Data
(
  type T = unit -> term list option
  val empty: T = fn () => raise Fail "Trace_Evaluation"
  fun init _ = empty
);
val trace_eval_cookie = (Trace_Evaluation.get, Trace_Evaluation.put, "Trace_Evaluation.put");
\<close>

definition [code]: "code_real_inv k \<equiv> Ratreal (rat_of_rational (Frct_integer (1, integer_of_nat k)))"
term "map_option snd"
ML \<open>fun check_cyphycircus_trace_prefix_ref_by ctxt stT evT breadth depth step_limit timestep_den has_tick spec impl = 
  let val actT = Type (@{type_name cyphyaction}, [evT, stT])
      val resT = Type (@{type_name option}, [HOLogic.mk_prodT (HOLogic.boolT, HOLogic.listT HOLogic.termT)])
      val cyphycircus_trace_prefix_ref_by = Const (@{const_name cyphycircus_trace_prefix_ref_by},
                HOLogic.natT --> HOLogic.realT --> stT --> (HOLogic.listT evT) --> HOLogic.boolT
                  --> actT --> actT --> HOLogic.natT --> HOLogic.natT --> resT)
      val map_option = Const (@{const_name map_option},
        (HOLogic.mk_prodT (HOLogic.boolT, HOLogic.listT HOLogic.termT) --> HOLogic.listT HOLogic.termT)
          --> resT
          --> Type (@{type_name option}, [HOLogic.listT HOLogic.termT]))
      val unpack_result = map_option
        $ Const (@{const_name snd}, HOLogic.mk_prodT (HOLogic.boolT, HOLogic.listT HOLogic.termT) --> HOLogic.listT HOLogic.termT)
      val term = cyphycircus_trace_prefix_ref_by
                  $ (HOLogic.mk_nat step_limit)
                  $ (@{term "code_real_inv"} $ (HOLogic.mk_nat timestep_den))
                  $ (Const (@{const_name default}, stT)) (* initial state *)
                  $ (HOLogic.mk_list evT [])
                  $ (if has_tick then @{term True} else @{term False})
                  $ spec
                  $ impl
                  $ (HOLogic.mk_nat breadth)
                  $ (HOLogic.mk_nat depth)
  in Code_Runtime.dynamic_value trace_eval_cookie ctxt NONE (Option.map o map) (unpack_result $ term) []
  end\<close>

term cyphycircus_trace_incremental_ref_by
ML \<open>fun check_cyphycircus_trace_incremental_ref_by ctxt stT evT breadth depth step_limit timestep_den has_tick spec impl = 
  let val actT = Type (@{type_name cyphyaction}, [evT, stT])
      val resT = Type (@{type_name option}, [HOLogic.mk_prodT (HOLogic.boolT, HOLogic.listT HOLogic.termT)])
      val cyphycircus_trace_incremental_ref_by = Const (@{const_name cyphycircus_trace_incremental_ref_by},
                HOLogic.natT --> HOLogic.realT --> stT --> stT --> HOLogic.boolT
                  --> actT --> actT --> HOLogic.natT --> HOLogic.natT --> resT)
      val map_option = Const (@{const_name map_option},
        (HOLogic.mk_prodT (HOLogic.boolT, HOLogic.listT HOLogic.termT) --> HOLogic.listT HOLogic.termT)
          --> resT
          --> Type (@{type_name option}, [HOLogic.listT HOLogic.termT]))
      val unpack_result = map_option
        $ Const (@{const_name snd}, HOLogic.mk_prodT (HOLogic.boolT, HOLogic.listT HOLogic.termT) --> HOLogic.listT HOLogic.termT)
      val term = cyphycircus_trace_incremental_ref_by
                  $ (HOLogic.mk_nat step_limit)
                  $ (@{term "code_real_inv"} $ (HOLogic.mk_nat timestep_den))
                  $ (Const (@{const_name default}, stT)) (* initial state for P *)
                  $ (Const (@{const_name default}, stT)) (* initial state for Q *)
                  $ (if has_tick then @{term True} else @{term False})
                  $ spec
                  $ impl
                  $ (HOLogic.mk_nat breadth)
                  $ (HOLogic.mk_nat depth)
  in Code_Runtime.dynamic_value trace_eval_cookie ctxt NONE (Option.map o map) (unpack_result $ term) []
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


lemma test1: "cyphycircus_trace_ref_by 10000 (code_real_inv 1000) (default::bar) t has_tick
    (a\<^bold>.1 \<rightarrow> a\<^bold>!2 \<rightarrow> Skip) (a\<^bold>.1 \<rightarrow> a\<^bold>!0 \<rightarrow> Skip)"
  apply (unfold cyphycircus_trace_ref_by_def, safe)
  quickcheck[expect=counterexample]
  oops

ML \<open>let val term_string = Pretty.pure_string_of o Syntax.pretty_term @{context}
        fun traceToString trace = String.concatWith " \<rightarrow> " (map term_string trace)
    in Option.map (Option.map traceToString) (check_cyphycircus_trace_prefix_ref_by @{context} @{typ bar} @{typ foo} 10 10 1000 100 false
      @{term "a\<^bold>.1 \<rightarrow> a\<^bold>!2 \<rightarrow> Skip :: (foo, bar) cyphyaction"}
      @{term "a\<^bold>.1 \<rightarrow> a\<^bold>!0 \<rightarrow> Skip :: (foo, bar) cyphyaction"})
    end\<close>

ML \<open>let val term_string = Pretty.pure_string_of o Syntax.pretty_term @{context}
        fun traceToString trace = String.concatWith " \<rightarrow> " (map term_string trace)
    in Option.map (Option.map traceToString) (check_cyphycircus_trace_incremental_ref_by @{context} @{typ bar} @{typ foo} 10 10 1000 100 false
      @{term "a\<^bold>.1 \<rightarrow> a\<^bold>!2 \<rightarrow> Skip :: (foo, bar) cyphyaction"}
      @{term "a\<^bold>.1 \<rightarrow> a\<^bold>!0 \<rightarrow> Skip :: (foo, bar) cyphyaction"})
    end\<close>

lemma test2: "cyphycircus_trace_ref_by 10000 (code_real_inv 1000) (default::bar) t has_tick
    (a\<^bold>.1 \<rightarrow> a\<^bold>!0 \<rightarrow>  Skip) (a\<^bold>.1 \<rightarrow> a\<^bold>?x \<rightarrow> Skip)"
  apply (unfold cyphycircus_trace_ref_by_def, safe)
  quickcheck[expect=counterexample]
  oops

ML \<open>let val term_string = Pretty.pure_string_of o Syntax.pretty_term @{context}
        fun traceToString trace = String.concatWith " \<rightarrow> " (map term_string trace)
    in Option.map (Option.map traceToString) (check_cyphycircus_trace_prefix_ref_by @{context} @{typ bar} @{typ foo} 10 10 1000 100 false
      @{term "a\<^bold>.1 \<rightarrow> a\<^bold>!0 \<rightarrow> Skip :: (foo, bar) cyphyaction"}
      @{term "a\<^bold>.1 \<rightarrow> a\<^bold>?x \<rightarrow> Skip :: (foo, bar) cyphyaction"})
    end\<close>

ML \<open>let val term_string = Pretty.pure_string_of o Syntax.pretty_term @{context}
        fun traceToString trace = String.concatWith " \<rightarrow> " (map term_string trace)
    in Option.map (Option.map traceToString) (check_cyphycircus_trace_incremental_ref_by @{context} @{typ bar} @{typ foo} 10 10 1000 100 false
      @{term "a\<^bold>.1 \<rightarrow> a\<^bold>!0 \<rightarrow> Skip :: (foo, bar) cyphyaction"}
      @{term "a\<^bold>.1 \<rightarrow> a\<^bold>?x \<rightarrow> Skip :: (foo, bar) cyphyaction"})
    end\<close>

recursive where "baz = b \<rightarrow> baz"

lemma test3: "cyphycircus_trace_ref_by 10000 (code_real_inv 1000) (default::bar) t has_tick
    (b \<rightarrow> Skip) baz"
  apply (unfold cyphycircus_trace_ref_by_def baz_def baz_rec_fun_def, safe)
  quickcheck[expect=counterexample]
  oops

ML \<open>let val term_string = Pretty.pure_string_of o Syntax.pretty_term @{context}
        fun traceToString trace = String.concatWith " \<rightarrow> " (map term_string trace)
    in Option.map (Option.map traceToString) (check_cyphycircus_trace_prefix_ref_by @{context} @{typ bar} @{typ foo} 10 10 1000 100 false
      @{term "b \<rightarrow> Skip :: (foo, bar) cyphyaction"}
      (Raw_Simplifier.rewrite_term @{theory} @{thms recursive_defs rec_sys_defs cyphyaction_datatype_unfolds} [] @{term "baz :: (foo, bar) cyphyaction"}))
    end\<close>

ML \<open>let val term_string = Pretty.pure_string_of o Syntax.pretty_term @{context}
        fun traceToString trace = String.concatWith " \<rightarrow> " (map term_string trace)
    in Option.map (Option.map traceToString) (check_cyphycircus_trace_incremental_ref_by @{context} @{typ bar} @{typ foo} 10 10 1000 100 false
      @{term "b \<rightarrow> Skip :: (foo, bar) cyphyaction"}
      (Raw_Simplifier.rewrite_term @{theory} @{thms recursive_defs rec_sys_defs cyphyaction_datatype_unfolds} [] @{term "baz :: (foo, bar) cyphyaction"}))
    end\<close>

lemma test4: "cyphycircus_trace_ref_by 10000 (code_real_inv 1000) (default::bar) t has_tick
    baz (b \<rightarrow> Skip)"
  apply (unfold cyphycircus_trace_ref_by_def baz_def baz_rec_fun_def, safe)
  quickcheck[expect=counterexample]
  oops

ML \<open>let val term_string = Pretty.pure_string_of o Syntax.pretty_term @{context}
        fun traceToString trace = String.concatWith " \<rightarrow> " (map term_string trace)
    in Option.map (Option.map traceToString) (check_cyphycircus_trace_prefix_ref_by @{context} @{typ bar} @{typ foo} 10 10 1000 100 true
      (Raw_Simplifier.rewrite_term @{theory} @{thms recursive_defs rec_sys_defs cyphyaction_datatype_unfolds} [] @{term "baz :: (foo, bar) cyphyaction"})
      @{term "b \<rightarrow> Skip :: (foo, bar) cyphyaction"})
    end\<close>

ML \<open>let val term_string = Pretty.pure_string_of o Syntax.pretty_term @{context}
        fun traceToString trace = String.concatWith " \<rightarrow> " (map term_string trace)
    in Option.map (Option.map traceToString) (check_cyphycircus_trace_incremental_ref_by @{context} @{typ bar} @{typ foo} 10 10 1000 100 true
      (Raw_Simplifier.rewrite_term @{theory} @{thms recursive_defs rec_sys_defs cyphyaction_datatype_unfolds} [] @{term "baz :: (foo, bar) cyphyaction"})
      @{term "b \<rightarrow> Skip :: (foo, bar) cyphyaction"})
    end\<close>

recursive where
  "test5_cont =
    (cEvolve (v +\<^sub>L time) (\<lambda>_. \<lparr>n\<^sub>v=0, v\<^sub>v=2, time\<^sub>v=1\<rparr>) (time < 1)\<^sub>e) ;; time := 0 ;;
    a\<^bold>!(nat (floor v)) \<rightarrow> test5_cont"
recursive where
  "test5_discr = n := n+2 ;; a\<^bold>!n \<rightarrow> test5_discr"

lemma test5: "cyphycircus_trace_ref_by 10000 (code_real_inv 1000) (default::bar) t has_tick
    test5_cont (a\<^bold>!2 \<rightarrow> a\<^bold>!0 \<rightarrow>  Skip)"
  apply (unfold cyphycircus_trace_ref_by_def
          test5_cont_def test5_cont_rec_fun_def test5_discr_def test5_discr_rec_fun_def, safe)
  quickcheck[expect=counterexample]
  oops

ML \<open>let val term_string = Pretty.pure_string_of o Syntax.pretty_term @{context}
        fun traceToString trace = String.concatWith " \<rightarrow> " (map term_string trace)
    in Option.map (Option.map traceToString) (check_cyphycircus_trace_prefix_ref_by @{context} @{typ bar} @{typ foo} 10 10 1000 100 false
      (@{term "test5_cont :: (foo, bar) cyphyaction"})
      @{term "a\<^bold>!2 \<rightarrow> a\<^bold>!0 \<rightarrow>  Skip :: (foo, bar) cyphyaction"})
    end\<close>

ML \<open>let val term_string = Pretty.pure_string_of o Syntax.pretty_term @{context}
        fun traceToString trace = String.concatWith " \<rightarrow> " (map term_string trace)
    in Option.map (Option.map traceToString) (check_cyphycircus_trace_incremental_ref_by @{context} @{typ bar} @{typ foo} 10 10 1000 100 false
      (@{term "test5_cont :: (foo, bar) cyphyaction"})
      @{term "a\<^bold>!2 \<rightarrow> a\<^bold>!0 \<rightarrow>  Skip :: (foo, bar) cyphyaction"})
    end\<close>

lemma test5': "cyphycircus_trace_ref_by 10 (code_real_inv 1000) (default::bar) t has_tick
    test5_cont (a\<^bold>!2 \<rightarrow> a\<^bold>!0 \<rightarrow>  Skip)"
  apply (unfold cyphycircus_trace_ref_by_def
          test5_cont_def test5_cont_rec_fun_def test5_discr_def test5_discr_rec_fun_def, safe)
  quickcheck[expect=no_counterexample]
  oops

ML \<open>let val term_string = Pretty.pure_string_of o Syntax.pretty_term @{context}
        fun traceToString trace = String.concatWith " \<rightarrow> " (map term_string trace)
    in Option.map (Option.map traceToString) (check_cyphycircus_trace_prefix_ref_by @{context} @{typ bar} @{typ foo} 10 10 10 100 false
      (@{term "test5_cont :: (foo, bar) cyphyaction"})
      @{term "a\<^bold>!2 \<rightarrow> a\<^bold>!0 \<rightarrow>  Skip :: (foo, bar) cyphyaction"})
    end\<close>

ML \<open>let val term_string = Pretty.pure_string_of o Syntax.pretty_term @{context}
        fun traceToString trace = String.concatWith " \<rightarrow> " (map term_string trace)
    in Option.map (Option.map traceToString) (check_cyphycircus_trace_incremental_ref_by @{context} @{typ bar} @{typ foo} 10 10 10 100 false
      (@{term "test5_cont :: (foo, bar) cyphyaction"})
      @{term "a\<^bold>!2 \<rightarrow> a\<^bold>!0 \<rightarrow>  Skip :: (foo, bar) cyphyaction"})
    end\<close>

hide_type foo bar

hide_const n v time a b

end
