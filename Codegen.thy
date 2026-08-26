theory Codegen
  imports Axiomatic_CyPhyCircus.Ax_CyPhyCircus
    Interaction_Trees.Interaction_Trees Interaction_Trees.ITree_Recursion
    ITree_Simulation.ITree_Simulation "HOL-Library.Code_Lazy"
    "HOL-Library.Multiset" "Framed_ODEs.Framed_ODEs" (*"HOL-Library.Code_Real_Approx_By_Float"*)
begin

unbundle Circus_Syntax
unbundle maplet_syntax

(* add some missing monotonicity axioms (needs moving to Axiomatic_CyPhyCircus.Ax_CyPhyCircus) *)
axiomatization where
  cSync_mono [mono_rule]: "\<lbrakk> P\<^sub>1 \<le> P\<^sub>2 \<rbrakk> \<Longrightarrow> c \<rightarrow> P\<^sub>1 \<le> c \<rightarrow> P\<^sub>2" and
  cInput_mono [mono_rule]: "\<lbrakk>\<And>x. F\<^sub>1 x \<le> F\<^sub>2 x \<rbrakk> \<Longrightarrow> c'\<^bold>?x \<rightarrow> F\<^sub>1 x \<le> c'\<^bold>?x \<rightarrow> F\<^sub>2 x" and
  cOutput_mono [mono_rule]: "\<lbrakk> P\<^sub>1 \<le> P\<^sub>2 \<rbrakk> \<Longrightarrow> c'\<^bold>!e \<rightarrow> P\<^sub>1 \<le> c'\<^bold>!e \<rightarrow> P\<^sub>2"

section \<open>Miscellaneous Codegen Setup\<close>

lemma pfun_lookup_map_code [code]:
  "pfun_lookup (pfun_of_map f) k = f k"
  by auto

code_lazy_type itree

code_printing
  type_constructor rational \<rightharpoonup> (SML) "Rat.rat"
  | class_instance rational :: "HOL.equal" \<rightharpoonup> (SML) -
  | constant "0 :: rational" \<rightharpoonup> (SML) "(Rat.of'_int 0)"
  | constant "1 :: rational" \<rightharpoonup> (SML) "(Rat.of'_int 1)"
  | constant "Code_Rational.term_of_rational_inst.term_of_rational" \<rightharpoonup>
    (SML) "(fn r => let val num = HOLogic.mk'_number HOLogic.intT (fst (Rat.dest r))
                        val den = HOLogic.mk'_number HOLogic.intT (snd (Rat.dest r))
                    in Const (\"Rat.Fract\", HOLogic.intT --> HOLogic.intT --> ratT) $ num $ den
                    end)"
  | constant "Frct_integer" \<rightharpoonup> (SML) "Rat.make (_)"
  | constant "HOL.equal :: rational \<Rightarrow> rational \<Rightarrow> bool" \<rightharpoonup>
    (SML) "(_) == (_)"
  |  constant "(<) :: rational \<Rightarrow> rational \<Rightarrow> bool" \<rightharpoonup>
    (SML) "_ < _"
  |  constant "(\<le>) :: rational \<Rightarrow> rational \<Rightarrow> bool" \<rightharpoonup>
    (SML) "_ <= _"
  | constant "(+) :: rational \<Rightarrow> rational \<Rightarrow> rational" \<rightharpoonup>
    (SML) "(_) + (_)"
  | constant "(-) :: rational \<Rightarrow> rational \<Rightarrow> rational" \<rightharpoonup>
    (SML) "(_) - (_)"
  | constant "(*) :: rational \<Rightarrow> rational \<Rightarrow> rational" \<rightharpoonup>
    (SML) "(_) * (_)"
  | constant "(/) :: rational \<Rightarrow> rational \<Rightarrow> rational" \<rightharpoonup>
    (SML) "(_) '/ (_)"
 | constant "uminus :: rational \<Rightarrow> rational" \<rightharpoonup>
    (SML) "Rat.neg"

code_printing
  constant numerator \<rightharpoonup> (SML) "(fst o Rat.dest)"
  | constant denominator \<rightharpoonup> (SML) "(snd o Rat.dest)"

code_printing
  constant "integer_power" \<rightharpoonup> (SML) "realpow"

ML \<open>fun digits_to_int [] = 0
      | digits_to_int (x :: xs) = 10 * (digits_to_int xs) + x\<close>
ML \<open>fun intpow x n = if n <= 0 then 1 else x * (intpow x (n-1))\<close>
ML \<open>fun realpow x n = if n <= 0 then 1.0 else x * (realpow x (n-1))\<close>

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
                Ratreal_const_pr,
                plus_const_pr,
                minus_const_pr,
                times_const_pr,
                uminus_const_pr,
                zero_const_pr,
                one_const_pr,
                term_of_const_pr,
                divide_const_pr
              ]
      in fold Code_Target.set_printings printings end\<close>


section \<open>Expressing sets of CyPhyCircus behaviour traces as itrees\<close>

datatype ('e, 's) cyphyevent =
    Event 'e \<comment>\<open> actual events from the trace \<close>
    | Timestep \<comment>\<open> evolution of time \<close>
    | WeakTimestep \<comment>\<open> evolution of time guaranteed not to change the state, does not need to be explored \<close>
    | StUpd 's \<comment>\<open> state update following a time step \<close>
    | Nondet nat \<comment>\<open> a branch of a nondeterministic choice \<close>


abbreviation "do_StUpd f ns s == Vis (map_pfun f
    (pfun_of_map (\<lambda>e. case e of
      StUpd s' \<Rightarrow>  if s' = s' \<triangleleft>\<^bsub>ns\<^esub> s then Some s' else None
    | _ \<Rightarrow> None)))"

abbreviation "restrict_StUpd ns s s' == if s' = s' \<triangleleft>\<^bsub>ns\<^esub> s then Some s' else None"

named_theorems cyphycircus_htree_defs

corec timed_deadlock :: "('a \<Longrightarrow> 's) \<Rightarrow> (('e, 's) cyphyevent, 's) htree" where
  "timed_deadlock ns s =
    Vis (map_pfun (\<lambda>_. do_StUpd (timed_deadlock ns) ns s) (pfun_of_alist [(WeakTimestep, ())] ))"

primcorec divergence :: "('e, 's) itree" where
  "divergence = Sil divergence"

corec event_prefix
    :: "('s \<Rightarrow> 'a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ( 'a \<Rightarrow> (('e, 's) cyphyevent, 's) htree) \<Rightarrow> ('b \<Longrightarrow> 's) \<Rightarrow> (('e, 's) cyphyevent, 's) htree" where
  "event_prefix c f ns s = Vis (map_pfun 
    (\<lambda>opt_val. case opt_val of
        None \<Rightarrow> do_StUpd (event_prefix c f ns) ns s
      | Some val \<Rightarrow> f val s)
    (pfun_of_map (\<lambda>te. case te of
        Event e \<Rightarrow> map_option Some (match\<^bsub>c s\<^esub> e)
      | WeakTimestep \<Rightarrow> Some None
      | _ \<Rightarrow> None)))"

abbreviation "orelse \<equiv> Quickcheck_Exhaustive.orelse"
notation orelse  (infixr \<open>orelse\<close> 55)

corecursive merge_extchoice
    :: "(('e, 's) cyphyevent, 's) itree \<Rightarrow> (('e, 's) cyphyevent, 's) itree
      \<Rightarrow> (('e, 's) cyphyevent, 's) itree" where
  "merge_extchoice P Q =
    (case (P, Q) of
      \<comment>\<open> Rets represent termination with a particular state,
          treat as a nondeterministic choice of Rets unless they are the same\<close>
      (Ret x, Ret y) \<Rightarrow> 
        (if x = y then
          Ret x
        else
          Vis (pfun_of_alist [(Nondet 0, Ret x), (Nondet 1, Ret y)] ))
      \<comment>\<open> Silent transitions happen immediately \<close>
    | (Ret x, Sil Q') \<Rightarrow> Sil (merge_extchoice (Ret x) Q')
      \<comment>\<open> The state update implicit in the Ret is added nondeterministically alongside the events from the Vis \<close>
    | (Ret x, Vis G) \<Rightarrow>
        Vis (pfun_of_map (\<lambda>e.
          \<comment>\<open> Try the events of the Vis \<close>
          (pfun_lookup G e)
            orelse
          \<comment>\<open> If that fails, try a Nondet for the Ret\<close>
          (case e of
            \<comment>\<open> This must be the minimal Nondet, so take this \<close>
            Nondet 0 \<Rightarrow> Some (Ret x)
            \<comment>\<open> Check that the previous Nondet is in the Vis to ensure minimality \<close>
          | Nondet (Suc n) \<Rightarrow> map_option (\<lambda>_. Ret x) (pfun_lookup G (Nondet n))
          | _ \<Rightarrow> None)))
      \<comment>\<open> Silent transitions happen immediately \<close>
    | (Sil P', Ret y) \<Rightarrow> Sil (merge_extchoice P' (Ret y))
      \<comment>\<open> Merge two silent transitions \<close>
    | (Sil P', Sil Q') \<Rightarrow> Sil (merge_extchoice P' Q')
      \<comment>\<open> Silent transitions happen immediately \<close>
    | (Sil P', Vis G) \<Rightarrow> Sil (merge_extchoice P' (Vis G))
      \<comment>\<open> The state update implicit in the Ret is added nondeterministically alongside the events from the Vis \<close>
    | (Vis F, Ret y) \<Rightarrow> 
        Vis (pfun_of_map (\<lambda>e.
          \<comment>\<open> Try the events of the Vis \<close>
          (pfun_lookup F e)
            orelse
          \<comment>\<open> If that fails, try a Nondet for the Ret\<close>
          (case e of
            \<comment>\<open> This must be the minimal Nondet, so take this \<close>
            Nondet 0 \<Rightarrow> Some (Ret y)
            \<comment>\<open> Check that the previous Nondet is in the Vis to ensure minimality \<close>
          | Nondet (Suc n) \<Rightarrow> map_option (\<lambda>_. Ret y) (pfun_lookup F (Nondet n))
          | _ \<Rightarrow> None)))
      \<comment>\<open> Silent transitions happen immediately \<close>
    | (Vis F, Sil Q') \<Rightarrow> Sil (merge_extchoice (Vis F) Q')
      \<comment>\<open> Merge events of the two sides - same events result in nondeterminism \<close>
    | (Vis F, Vis G) \<Rightarrow> Vis (map_pfun 
        (\<lambda>opt_itrees. case opt_itrees of
            (None, Some Q) \<Rightarrow> Q
          | (Some P, None) \<Rightarrow> P
          | (Some P, Some Q) \<Rightarrow> merge_extchoice P Q)
        (pfun_of_map (\<lambda>e. case e of
            \<comment>\<open> Timesteps have to occur on both sides - check for a merge of weak timesteps \<close>
            Timestep \<Rightarrow> (case (pfun_lookup F Timestep, pfun_lookup F WeakTimestep,
                                pfun_lookup G Timestep, pfun_lookup G WeakTimestep) of
                (Some P, _, Some Q, _) \<Rightarrow> Some (Some P, Some Q) \<comment>\<open>merge strong time steps, ignore the weak ones\<close>
              | (None, Some P, Some Q, _) \<Rightarrow> Some (Some P, Some Q) \<comment>\<open>upgrade weak timestep on left\<close>
              | (Some P, _, None, Some Q) \<Rightarrow> Some (Some P, Some Q) \<comment>\<open>upgrade weak timestep on right\<close>
              | _ \<Rightarrow> None) \<comment>\<open>can't output a strong timestep if there isn't at least one already there\<close>
          | WeakTimestep \<Rightarrow> (case (pfun_lookup F Timestep, pfun_lookup F WeakTimestep,
                                pfun_lookup G Timestep, pfun_lookup G WeakTimestep) of
                (Some P, _, Some Q, _) \<Rightarrow> None \<comment>\<open>merge strong time steps, ignore the weak ones\<close>
              | (None, Some P, Some Q, _) \<Rightarrow> None \<comment>\<open>upgrade weak timestep on left\<close>
              | (Some P, _, None, Some Q) \<Rightarrow> None \<comment>\<open>upgrade weak timestep on right\<close>
              | (None, Some P, None, Some Q) \<Rightarrow> Some (Some P, Some Q) \<comment>\<open>merge weak timesteps if there are no strong ones\<close>
              | _ \<Rightarrow> None)
            \<comment>\<open> Other events can be on either or both sides 
                - same events push the merge down
                - same state updates don't resolve the choice
                - same nondeterminisms push the nondeterminism down\<close>
          | e \<Rightarrow> (case (pfun_lookup F e, pfun_lookup G e) of
                (None, None) \<Rightarrow> None
              | (opt_P, opt_Q) \<Rightarrow> Some (opt_P, opt_Q)))))
    )" .

corecursive merge_parallel
  :: "'s \<Rightarrow> ('a \<Longrightarrow> 's) \<Rightarrow> ('b \<Longrightarrow> 's) \<Rightarrow> ('c \<Longrightarrow> 's) \<Rightarrow> 'e set \<Rightarrow> (('e, 's) cyphyevent, 's) itree \<Rightarrow> (('e, 's) cyphyevent, 's) itree
    \<Rightarrow> (('e, 's) cyphyevent, 's) itree" where
  "merge_parallel st0 ns ns1 ns2 cs P Q =
    (case (P, Q) of
      \<comment>\<open> If both processes are ready to terminate,
          they terminate with a merge of the state \<close>
      (Ret st1, Ret st2) \<Rightarrow> Ret (st0 \<triangleleft>\<^bsub>ns1\<^esub> st1 \<triangleleft>\<^bsub>ns2\<^esub> st2)
      \<comment>\<open> Silent transitions happen immediately \<close>
    | (Ret st1, Sil Q') \<Rightarrow> Sil (merge_parallel st0 ns ns1 ns2 cs (Ret st1) Q')
      \<comment>\<open> RHS isn't ready to terminate, carry on through RHS \<close>
    | (Ret st1, Vis G) \<Rightarrow> Vis (map_pfun (merge_parallel st0 ns ns1 ns2 cs (Ret st1)) G)
      \<comment>\<open> Silent transitions happen immediately \<close>
    | (Sil P', Ret st2) \<Rightarrow> Sil (merge_parallel st0 ns ns1 ns2 cs P' (Ret st2))
      \<comment>\<open> Merge two silent transitions \<close>
    | (Sil P', Sil Q') \<Rightarrow> Sil (merge_parallel st0 ns ns1 ns2 cs P' Q')
      \<comment>\<open> Silent transitions happen immediately \<close>
    | (Sil P', Vis G) \<Rightarrow> Sil (merge_parallel st0 ns ns1 ns2 cs P' (Vis G))
      \<comment>\<open> LHS isn't ready to terminate, carry on through LHS \<close>
    | (Vis F, Ret st2) \<Rightarrow> Vis (map_pfun (\<lambda>P. merge_parallel st0 ns ns1 ns2 cs P (Ret st2)) F)
      \<comment>\<open> Silent transitions happen immediately \<close>
    | (Vis F, Sil Q') \<Rightarrow> Sil (merge_parallel st0 ns ns1 ns2 cs (Vis F) Q')
      \<comment>\<open> Merge the events depending on their types \<close>
    | (Vis F, Vis G) \<Rightarrow> Vis (map_pfun 
        (\<lambda>opt_itrees. case opt_itrees of
            (None, Some Q) \<Rightarrow> Q
          | (Some P, None) \<Rightarrow> P
          | (Some P, Some Q) \<Rightarrow> merge_parallel st0 ns ns1 ns2 cs P Q)
        (pfun_of_map (\<lambda>e. case e of
          \<comment>\<open> actual events are merged based on whether they require synchronisation \<close>
          (Event e) \<Rightarrow> (if e \<in> cs then
            case (pfun_lookup F (Event e), pfun_lookup G (Event e)) of
              (Some P', Some Q') \<Rightarrow> Some (Some P', Some Q')
            | _ \<Rightarrow> None
          else
            (case (pfun_lookup F (Event e), pfun_lookup G (Event e)) of
              (None, None) \<Rightarrow> None
            | x \<Rightarrow> Some x))
          \<comment>\<open> state updates are merged according to the nameset and must agree
              - can be arbitrary outside ns
              - must keep st0 inside ns but outside ns1 and ns2
              - P and Q are restricted by their own namesets\<close>
        | StUpd s' \<Rightarrow>
            (if st0 = st0 \<triangleleft>\<^bsub>ns\<^esub> s' \<triangleleft>\<^bsub>ns1\<^esub> st0 \<triangleleft>\<^bsub>ns2\<^esub> st0 \<comment>\<open> must keep st0 inside ns but outside ns1 and ns2 \<close>
            then (case (pfun_lookup F (StUpd s'), pfun_lookup G (StUpd s')) of
                    (Some P', Some Q') \<Rightarrow> Some (Some P', Some Q')
                  | _ \<Rightarrow> None)
            else None) 
          \<comment>\<open> timesteps require synchronisation - check for a merge of weak timesteps\<close>
          | Timestep \<Rightarrow> (case (pfun_lookup F Timestep, pfun_lookup F WeakTimestep,
                                pfun_lookup G Timestep, pfun_lookup G WeakTimestep) of
                (Some P, _, Some Q, _) \<Rightarrow> Some (Some P, Some Q) \<comment>\<open>merge strong time steps, ignore the weak ones\<close>
              | (None, Some P, Some Q, _) \<Rightarrow> Some (Some P, Some Q) \<comment>\<open>upgrade weak timestep on left\<close>
              | (Some P, _, None, Some Q) \<Rightarrow> Some (Some P, Some Q) \<comment>\<open>upgrade weak timestep on right\<close>
              | _ \<Rightarrow> None) \<comment>\<open>can't output a strong timestep if there isn't at least one already there\<close>
          | WeakTimestep \<Rightarrow> (case (pfun_lookup F Timestep, pfun_lookup F WeakTimestep,
                                pfun_lookup G Timestep, pfun_lookup G WeakTimestep) of
                (Some P, _, Some Q, _) \<Rightarrow> None \<comment>\<open>merge strong time steps, ignore the weak ones\<close>
              | (None, Some P, Some Q, _) \<Rightarrow> None \<comment>\<open>upgrade weak timestep on left\<close>
              | (Some P, _, None, Some Q) \<Rightarrow> None \<comment>\<open>upgrade weak timestep on right\<close>
              | (None, Some P, None, Some Q) \<Rightarrow> Some (Some P, Some Q) \<comment>\<open>merge weak timesteps if there are no strong ones\<close>
              | _ \<Rightarrow> None)
          \<comment>\<open> nondeterminisms aren't synchronised \<close>
        | (Nondet n) \<Rightarrow> (case (pfun_lookup F (Nondet n), pfun_lookup G (Nondet n)) of
              (None, None) \<Rightarrow> None
            | x \<Rightarrow> Some x))))
    )" .

context
begin
no_notation Abstract_Prog_Syntax.useq (infixr ";" 55)

abbreviation "RKstep f h y \<equiv>
  let k1 = f y;
      k2 = f (y + ((h / 2) *\<^sub>R k1));
      k3 = f (y + ((h / 2) *\<^sub>R k2));
      k4 = f (y + h *\<^sub>R k3)
  in y + (h / 6) *\<^sub>R (k1 + 2*\<^sub>Rk2 + 2*\<^sub>Rk3 + 2*\<^sub>Rk4)"

end

corec evolve :: "('r::real_normed_vector \<Longrightarrow> 's) \<Rightarrow> ('s \<Rightarrow> 's) \<Rightarrow> ('s \<Rightarrow> \<bool>) \<Rightarrow> real \<Rightarrow> ('b \<Longrightarrow> 's) \<Rightarrow> (('e, 's) cyphyevent, 's) htree" where
  "evolve v f pred timestep ns s =
    (if pred s then
      Vis (map_pfun
            (\<lambda> _. Vis (map_pfun
              (evolve v f pred timestep ns)
              (pfun_of_map
                (\<lambda>e. case e of 
                    StUpd s' \<Rightarrow>
                      (if s' = put\<^bsub>v\<^esub> (s' \<triangleleft>\<^bsub>ns\<^esub> s) (RKstep (\<lambda>x. get\<^bsub>v\<^esub> (f (put\<^bsub>v\<^esub> s x)) ) timestep (get\<^bsub>v\<^esub>s)) then
                        Some s'
                      else
                        None)
                  | _ \<Rightarrow> None))))
            (pfun_of_alist [(Timestep, ())] )
          )
    else
      Ret s)"

axiomatization htree_of :: "('e, 's) cyphyaction \<Rightarrow> real \<Rightarrow> ('b \<Longrightarrow> 's) \<Rightarrow> (('e, 's) cyphyevent, 's) htree" where
  htree_of_Evolve[cyphycircus_htree_defs]:
    "htree_of (cEvolve v subst pred) timestep ns s = evolve v subst pred timestep ns s" and
  htree_of_Stop[cyphycircus_htree_defs]:
    "htree_of Stop timestep ns = timed_deadlock ns" and
  htree_of_Chaos[cyphycircus_htree_defs]:
    "htree_of Chaos timestep ns s = divergence" and
  htree_of_Assume[cyphycircus_htree_defs]:
    "htree_of (cAssume pred) timestep ns s = (if pred s then Ret s else divergence)" and
  htree_of_Assigns[cyphycircus_htree_defs]:
    "htree_of (cAssigns subst) timestep ns s = Ret (s \<triangleleft>\<^bsub>ns\<^esub> (subst s))" and
  htree_of_SyncPrefix[cyphycircus_htree_defs]:
    "htree_of (e \<rightarrow> P) timestep ns = event_prefix (\<lambda>_. e) (\<lambda>_. htree_of P timestep ns) ns" and
  htree_of_InputPrefix[cyphycircus_htree_defs]:
    "htree_of (c\<^bold>?x \<rightarrow> (F x)) timestep ns = event_prefix (\<lambda>_. c) (\<lambda>x. htree_of (F x) timestep ns) ns" and
  htree_of_OutputPrefix[cyphycircus_htree_defs]:
    "htree_of (cOutputPrefix c expr P) timestep ns =
      event_prefix (\<lambda>s. c\<^bold>.(expr s)) (\<lambda>_. htree_of P timestep ns) ns" and
  htree_of_Seq[cyphycircus_htree_defs]:
    "htree_of (cSeq P Q) timestep ns s = (htree_of P timestep ns s) \<bind> (htree_of Q timestep ns)" and
  htree_of_Guard[cyphycircus_htree_defs]:
    "htree_of (cGuard pred P) timestep ns s =
      (if pred s then htree_of P timestep ns s else htree_of Stop timestep ns s)" and
  htree_of_Cond[cyphycircus_htree_defs]:
    "htree_of (cCond P pred Q) timestep ns s =
      (if pred s then htree_of P timestep ns s else htree_of Q timestep ns s)" and
  htree_of_ExtChoice[cyphycircus_htree_defs]:
    "htree_of (cExtChoice P Q) timestep ns s =
      merge_extchoice (htree_of P timestep ns s) (htree_of Q timestep ns s)" and
  htree_of_IntChoice[cyphycircus_htree_defs]:
    "htree_of (inf P Q) timestep ns s =
      Vis (pfun_of_alist  [(Nondet 0, htree_of P timestep ns s), (Nondet 1, htree_of Q timestep ns s)] )" and
  htree_of_ParComp[cyphycircus_htree_defs]:
    "htree_of (cParallelAct ns1 ns2 cs P Q) timestep ns s =
      merge_parallel s ns ns1 ns2 cs (htree_of P timestep ns s) (htree_of Q timestep ns s)"
for P Q :: "('e, 's) cyphyaction"
and s :: 's
and F :: "'a \<Rightarrow> ('e, 's) cyphyaction"
and c :: "'a \<Longrightarrow>\<^sub>\<triangle> 'e"
and expr :: "'s \<Rightarrow> 'a"
and pred :: "'s \<Rightarrow> bool"
and subst :: "'s \<Rightarrow> 's"
and timestep :: real
and ns :: "'b \<Longrightarrow> 's"
and ns1 :: "'c \<Longrightarrow> 's"
and ns2 :: "'d \<Longrightarrow> 's"
and v :: "'r::real_normed_vector \<Longrightarrow> 's"

lemma htree_of_Skip[cyphycircus_htree_defs]:
    "htree_of cSkip timestep ns s = Ret (s \<triangleleft>\<^bsub>ns\<^esub> s)"
  by (simp add: cSkip_def htree_of_Assigns)

subsection \<open>Handling of recursion\<close>

axiomatization lift_cyphyaction_fun
  :: "real \<Rightarrow> ('b \<Longrightarrow> 's) \<Rightarrow> (('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction)
      \<Rightarrow> ((('e, 's) cyphyevent, 's) htree \<Rightarrow> (('e, 's) cyphyevent, 's) htree)" where
  lift_cyphyaction_fun_id[cyphycircus_htree_defs]: "lift_cyphyaction_fun timestep ns (\<lambda>P. P) p = p" and
  lift_cyphyaction_fun_Evolve[cyphycircus_htree_defs]:
    "lift_cyphyaction_fun timestep ns (\<lambda>_. cEvolve v subst pred) p = htree_of (cEvolve v subst pred) timestep ns" and
  lift_cyphyaction_fun_Stop[cyphycircus_htree_defs]:
    "lift_cyphyaction_fun timestep ns (\<lambda>_. Stop) p = htree_of Stop timestep ns" and
  lift_cyphyaction_fun_Chaos[cyphycircus_htree_defs]:
    "lift_cyphyaction_fun timestep ns (\<lambda>_. Chaos) p = htree_of Chaos timestep ns" and
  lift_cyphyaction_fun_Assume[cyphycircus_htree_defs]:
    "lift_cyphyaction_fun timestep ns (\<lambda>_. cAssume pred) p = htree_of (cAssume pred) timestep ns" and
   lift_cyphyaction_fun_Assigns[cyphycircus_htree_defs]:
    "lift_cyphyaction_fun timestep ns (\<lambda>_. cAssigns subst) p = htree_of (cAssigns subst) timestep ns" and
  lift_cyphyaction_fun_SyncPrefix[cyphycircus_htree_defs]:
    "lift_cyphyaction_fun timestep ns (\<lambda>P. e \<rightarrow> F P) p = event_prefix (\<lambda>_. e) (\<lambda>_. lift_cyphyaction_fun timestep ns F p)  ns" and
  lift_cyphyaction_fun_InputPrefix[cyphycircus_htree_defs]:
    "lift_cyphyaction_fun timestep ns (\<lambda>P. c\<^bold>?x \<rightarrow> (Fa P x)) p =
      event_prefix (\<lambda>_. c) (\<lambda>x. lift_cyphyaction_fun timestep ns (\<lambda>P. Fa P x) p) ns" and
  lift_cyphyaction_fun_OutputPrefix[cyphycircus_htree_defs]:
    "lift_cyphyaction_fun timestep ns (\<lambda>P. cOutputPrefix c expr (F P)) p =
      event_prefix (\<lambda>s. c\<^bold>.(expr s)) (\<lambda>_. lift_cyphyaction_fun timestep ns F p) ns" and
  lift_cyphyaction_fun_Seq[cyphycircus_htree_defs]:
    "lift_cyphyaction_fun timestep ns (\<lambda>P. cSeq (F P) (G P)) p s =
      (lift_cyphyaction_fun  timestep ns F p s) \<bind> (lift_cyphyaction_fun timestep ns G p)" and
  lift_cyphyaction_fun_Guard[cyphycircus_htree_defs]:
    "lift_cyphyaction_fun timestep ns (\<lambda>P. cGuard pred (F P)) p s =
      (if pred s then lift_cyphyaction_fun timestep ns F p s else htree_of Stop timestep ns s)" and
  lift_cyphyaction_fun_Cond[cyphycircus_htree_defs]:
    "lift_cyphyaction_fun timestep ns (\<lambda>P. cCond (F P) pred (G P)) p s =
      (if pred s then lift_cyphyaction_fun timestep ns F p s else lift_cyphyaction_fun timestep ns G p s)" and
  lift_cyphyaction_fun_ExtChoice[cyphycircus_htree_defs]:
    "lift_cyphyaction_fun timestep ns (\<lambda>P. cExtChoice (F P) (G P)) p s =
      merge_extchoice (lift_cyphyaction_fun timestep ns F p s) (lift_cyphyaction_fun timestep ns G p s)" and
  lift_cyphyaction_fun_IntChoice[cyphycircus_htree_defs]:
    "lift_cyphyaction_fun timestep ns (\<lambda>P. inf (F P) (G P)) p s = 
      Vis (pfun_of_alist  [(Nondet 0, lift_cyphyaction_fun timestep ns F p s), (Nondet 1, lift_cyphyaction_fun timestep ns G p s)] )"
  for 
    F G :: "('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction"
    and Fa :: "('e, 's) cyphyaction \<Rightarrow> 'a \<Rightarrow> ('e, 's) cyphyaction"
    and p :: "(('e, 's) cyphyevent, 's) htree"
    and s :: 's
    and c :: "'a \<Longrightarrow>\<^sub>\<triangle> 'e"
    and expr :: "'s \<Rightarrow> 'a"
    and pred :: "'s \<Rightarrow> bool"
    and subst :: "'s \<Rightarrow> 's"
    and v :: "'r::real_normed_vector \<Longrightarrow> 's"

primrec iterate_itree_fun
    :: "((('e, 's) cyphyevent, 's) htree \<Rightarrow> (('e, 's) cyphyevent, 's) htree) \<Rightarrow> nat \<Rightarrow> (('e, 's) cyphyevent, 's) htree" where
  "iterate_itree_fun f 0 s = divergence" |
  "iterate_itree_fun f (Suc n) s = f (iterate_itree_fun f n) s"


axiomatization where htree_of_Rec[cyphycircus_htree_defs]:
    "htree_of (\<nu> F) timestep ns s =
      Vis (pfun_of_map (\<lambda>e. case e of
          Nondet n \<Rightarrow> Some (iterate_itree_fun (lift_cyphyaction_fun timestep ns F) (Suc n) s)
        | _ \<Rightarrow> None))"
  for F :: "('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction"
    and s :: 's
    and ns :: "'b \<Longrightarrow> 's"

section \<open>Generating sequences of states for CyPhyCircus actions\<close>

fun event_prefix_states :: "nat \<Rightarrow> nat list \<Rightarrow> 's option list" where
  "event_prefix_states len branches =
      (case branches of
        [] \<Rightarrow> []
      | (x # xs) \<Rightarrow> replicate (min x len) None)"

fun select_input_event :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> 'e list \<Rightarrow> nat \<Rightarrow> ('a \<times> 'e list) option"  where
  "select_input_event c [] n = None" |
  "select_input_event c (e # t) 0 =
      (case match\<^bsub>c\<^esub> e of
        None \<Rightarrow> select_input_event c t 0 \<comment>\<open>not the event we want, try the next\<close>
      | Some a \<Rightarrow> Some (a, t))" |
  "select_input_event c (e # t) (Suc n) =
      (case match\<^bsub>c\<^esub> e of
        None \<Rightarrow> select_input_event c t (Suc n)  \<comment>\<open>not the event we want, try the next but don't decrement\<close>
      | Some _ \<Rightarrow> select_input_event c t n \<comment>\<open>is the event we want, but we decrement and skip it to allow for parallelism\<close>)"

fun merge_parallel_states :: "('a \<Longrightarrow> 's) \<Rightarrow> ('b \<Longrightarrow> 's) \<Rightarrow> 's \<Rightarrow> 's option list \<Rightarrow> 's option list \<Rightarrow> 's option list" where
  "merge_parallel_states ns1 ns2 s [] ys = []" |
  "merge_parallel_states ns1 ns2 s xs [] = []" |
  "merge_parallel_states ns1 ns2 s (None # xs) (None # ys) =
    None # merge_parallel_states ns1 ns2 s xs ys" |
  "merge_parallel_states ns1 ns2 s (Some x # xs) (None # ys) =
    Some (s \<triangleleft>\<^bsub>ns1\<^esub> x) # merge_parallel_states ns1 ns2 (s \<triangleleft>\<^bsub>ns1\<^esub> x) xs ys" |
  "merge_parallel_states ns1 ns2 s (None # xs) (Some y # ys) =
    Some (s \<triangleleft>\<^bsub>ns2\<^esub> y) # merge_parallel_states ns1 ns2 (s \<triangleleft>\<^bsub>ns2\<^esub> y) xs ys" |
  "merge_parallel_states ns1 ns2 s (Some x # xs) (Some y # ys) =
    Some (s \<triangleleft>\<^bsub>ns1\<^esub> x \<triangleleft>\<^bsub>ns2\<^esub> y) # merge_parallel_states ns1 ns2 (s \<triangleleft>\<^bsub>ns1\<^esub> x \<triangleleft>\<^bsub>ns2\<^esub> y) xs ys"

fun iterate_state_fun :: "('s \<Rightarrow> 's option list \<times> 's) \<Rightarrow> nat \<Rightarrow> 's \<Rightarrow> 's option list \<times> 's" where
  "iterate_state_fun f 0 s = ([], s)" |
  "iterate_state_fun f (Suc n) s =
    (case f s of (sts, ret) \<Rightarrow> apfst ((@) sts) (iterate_state_fun f n ret))"

abbreviation evolve_state_step :: "('r::real_normed_vector \<Longrightarrow> 's) \<Rightarrow> ('s \<Rightarrow> 's) \<Rightarrow> ('s \<Rightarrow> \<bool>) \<Rightarrow> real \<Rightarrow> 's \<Rightarrow> 's option list \<times> 's" where
  "evolve_state_step v f pred timestep s ==
    (if pred s then 
      (\<lambda>s'. ([Some s'], s'))
      (put\<^bsub>v\<^esub> s (RKstep (\<lambda>x. get\<^bsub>v\<^esub> (f (put\<^bsub>v\<^esub> s x)) ) timestep (get\<^bsub>v\<^esub>s)))
    else
       ([], s))"

axiomatization
  StUpds_of :: "('e, 's) cyphyaction \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> 'e list \<Rightarrow> 's \<Rightarrow> 's option list \<times> 's" where
  StUpds_of_Evolve[cyphycircus_htree_defs]:
    "StUpds_of (cEvolve v subst pred) timestep len branches t s =
      iterate_state_fun (evolve_state_step v subst pred timestep) len s" and
  StUpds_of_Stop[cyphycircus_htree_defs]:
    "StUpds_of Stop timestep len branches t = (\<lambda>s.  ([], s))" and
  StUpds_of_Chaos[cyphycircus_htree_defs]:
    "StUpds_of Chaos timestep len branches t = (\<lambda>s. ([], s))" and
  StUpds_of_Assume[cyphycircus_htree_defs]:
    "StUpds_of (cAssume pred) timestep len branches t = (\<lambda>s. ([], s))" and
  StUpds_of_Assigns[cyphycircus_htree_defs]:
    "StUpds_of (cAssigns subst) timestep len branches t = (\<lambda>s. ([], subst s))" and
  StUpds_of_SyncPrefix[cyphycircus_htree_defs]:
    "StUpds_of (e \<rightarrow> P) timestep len branches t s =
      (case StUpds_of P timestep len (tl branches) t s of
        (sts, ret) \<Rightarrow> (event_prefix_states len branches @ sts, ret))" and
  StUpds_of_InputPrefix[cyphycircus_htree_defs]:
    "StUpds_of (c\<^bold>?x \<rightarrow> (F x)) timestep len branches t = (\<lambda>s.  
      (case select_input_event c t (case_list 0 (\<lambda> x xs. x) branches) of 
        Some (a, t) \<Rightarrow>
          (case StUpds_of (F a) timestep len (tl (tl branches)) t s of
            (sts, ret) \<Rightarrow> (event_prefix_states len (tl branches) @ sts, ret))
      | None \<Rightarrow> ([], s)))" and
  StUpds_of_OutputPrefix[cyphycircus_htree_defs]:
    "StUpds_of (cOutputPrefix c expr P) timestep len branches t = (\<lambda>s.  
      (case StUpds_of P timestep len (tl branches) t s of
        (sts, ret) \<Rightarrow> (event_prefix_states len branches @ sts, ret)))" and
  StUpds_of_Seq[cyphycircus_htree_defs]:
    "StUpds_of (cSeq P Q) timestep len branches t = (\<lambda>s.  
      (case StUpds_of P timestep len branches t s of
        (sts, ret) \<Rightarrow> apfst ((@) sts) (StUpds_of Q timestep len branches t s)))" and
  StUpds_of_Guard[cyphycircus_htree_defs]:
    "StUpds_of (cGuard pred P) timestep len branches t = (\<lambda>s.  
      (if pred s then
        StUpds_of P timestep len branches t s
      else
        StUpds_of Stop timestep len branches t s))" and
  StUpds_of_Cond[cyphycircus_htree_defs]:
    "StUpds_of (cCond P pred Q) timestep len branches t = (\<lambda>s.  
      (if pred s then
        StUpds_of P timestep len branches t s
      else
        StUpds_of Q timestep len branches t s))" and
  StUpds_of_ExtChoice[cyphycircus_htree_defs]:
    "StUpds_of (cExtChoice P Q) timestep len branches t = (\<lambda>s.  
      (if even (case_list 0 (\<lambda> x xs. x) branches) then
        StUpds_of P timestep len (tl branches) t s
      else
        StUpds_of Q timestep len (tl branches) t s))" and
  StUpds_of_IntChoice[cyphycircus_htree_defs]:
    "StUpds_of (inf P Q) timestep len branches t = (\<lambda>s.  
      (if even (case_list 0 (\<lambda> x xs. x) branches) then
        StUpds_of P timestep len (tl branches) t s
      else
        StUpds_of Q timestep len (tl branches) t s))" and
  StUpds_of_ParComp[cyphycircus_htree_defs]:
    "StUpds_of (cParallelAct ns1 ns2 cs P Q) timestep len branches t = (\<lambda>s.  
      (case (StUpds_of P timestep len branches t s, StUpds_of Q timestep len branches t s) of
        ((sts1, ret1), (sts2, ret2)) \<Rightarrow> (merge_parallel_states ns1 ns2 s sts1 sts2, s \<triangleleft>\<^bsub>ns1\<^esub> ret1 \<triangleleft>\<^bsub>ns2\<^esub> ret2)))" and
  StUpds_of_Rec[cyphycircus_htree_defs]:
    "StUpds_of (\<nu> F) timestep len branches t =
      iterate_state_fun (StUpds_of (F Skip) timestep len branches t) len"

lemma StUpds_of_Skip[cyphycircus_htree_defs]:
    "StUpds_of (cSkip) timestep len branches t s = ([], s)"
  unfolding StUpds_of_Assigns cSkip_def by simp
  
section \<open>Checking trace refinement\<close>

context
begin
no_notation Abstract_Prog_Syntax.useq (infixr ";" 55)

fun itree_has_trace :: "nat \<Rightarrow> nat \<Rightarrow> 's list \<Rightarrow> 'e list \<Rightarrow> bool \<Rightarrow> (('e, 's) cyphyevent, 's) itree \<Rightarrow> bool option" where
  (* if the process terminates, then it only has the empty trace (with or without a tick) *)
  "itree_has_trace tau_bound choice_bound s t has_tick (Ret x) = Some (t = [])" |
  (* A silent transition when we have reached our tau bound causes checking to bail out *)
  "itree_has_trace 0 choice_bound s t has_tick (Sil P) = None" |
  (* A silent transition before our tau bound causes checking to pass through,
      decrementing the tau bound *)
  "itree_has_trace (Suc tau_bound) choice_bound s t has_tick (Sil P) =
      itree_has_trace tau_bound choice_bound s t has_tick P" |
  (* Visible behaviour always has the empty trace without tick *)
  "itree_has_trace tau_bound choice_bound s [] False (Vis F) = Some True" |
  (* Visible behaviour only has the empty trace with tick if it is reached through some nondeterminism or timestep *)
  "itree_has_trace tau_bound choice_bound s [] True (Vis F) = (
        \<comment> \<open>try a timestep with the next state if there is one\<close>
    let can_check_timestep = pfun_lookup F Timestep;
        check_timestep = can_check_timestep \<bind>
            (\<lambda>P2. case P2 of
                Vis F2 \<Rightarrow> (case s of
                    s0 # s' \<Rightarrow> (pfun_lookup F2 (StUpd s0)) \<bind>
                        (\<lambda> P3. case tau_bound of
                            0 \<Rightarrow> None
                          | Suc bound \<Rightarrow> 
                              itree_has_trace bound choice_bound s' [] True P3)
                  | [] \<Rightarrow> None)
              | _ \<Rightarrow> None);
        \<comment> \<open>go through the nondeterminsims to see if any of them succeed\<close>
        can_check_nondets = 
          fold 
            (\<lambda>x xs. case (x, xs) of
                (Some x, Some xs) \<Rightarrow> Some (x # xs)
              | (Some x, None) \<Rightarrow> Some [x]
              | (None, xs) \<Rightarrow> xs)
            (map (\<lambda>n. pfun_lookup F (Nondet n)) (upt 0 (Suc choice_bound)))
            None;
        check_nondets =
          can_check_nondets \<bind>
            (\<lambda> Ps. fold
              (combine_options disj)
              (map
                (\<lambda>P. case tau_bound of
                    0 \<Rightarrow> None
                  | Suc bound \<Rightarrow>
                      itree_has_trace bound choice_bound s [] True P)
                Ps)
              None)
    in case combine_options disj check_timestep check_nondets of
        None \<Rightarrow> 
          \<comment> \<open>the event wasn't there, but we may just not have checked far enough
                  - are there any other branches?\<close>
          (case (can_check_timestep, can_check_nondets) of
              \<comment> \<open>no other branches we can check - preserve False from event\<close>
              (None, None) \<Rightarrow> Some False
              \<comment> \<open>have other branches we can check, but they must have returned None\<close>
            | _ \<Rightarrow> None)
      | Some x \<Rightarrow> Some x)" |
  "itree_has_trace tau_bound choice_bound s (e # t) has_tick (Vis F) = (
     let check_event =
          (case pfun_lookup F (Event e) of 
            None \<Rightarrow> Some False
          | Some P \<Rightarrow> itree_has_trace tau_bound choice_bound s t has_tick P);
        can_check_timestep = pfun_lookup F Timestep;
        check_timestep = can_check_timestep \<bind>
            (\<lambda>P2. case P2 of
                Vis F2 \<Rightarrow> (case s of
                    s0 # s' \<Rightarrow> (pfun_lookup F2 (StUpd s0)) \<bind>
                        (\<lambda> P3. case tau_bound of
                            0 \<Rightarrow> None
                          | Suc bound \<Rightarrow> 
                              itree_has_trace bound choice_bound s' (e # t) has_tick P3)
                  | [] \<Rightarrow> None)
              | _ \<Rightarrow> None);
        \<comment> \<open>go through the nondeterminsims to see if any of them succeed\<close>
        can_check_nondets = 
          fold 
            (\<lambda>x xs. case (x, xs) of
                (Some x, Some xs) \<Rightarrow> Some (x # xs)
              | (Some x, None) \<Rightarrow> Some [x]
              | (None, xs) \<Rightarrow> xs)
            (map (\<lambda>n. pfun_lookup F (Nondet n)) (upt 0 (Suc choice_bound)))
            None;
        check_nondets =
          can_check_nondets \<bind>
            (\<lambda> Ps. fold
              (combine_options disj)
              (map
                (\<lambda>P. case tau_bound of
                    0 \<Rightarrow> None
                  | Suc bound \<Rightarrow>
                      itree_has_trace bound choice_bound s (e # t) has_tick P)
                Ps)
              None)
      in (case (check_event, combine_options disj check_timestep check_nondets) of
            (None, None) \<Rightarrow> None
          | (None, Some y) \<Rightarrow> Some y
          | (Some True, None) \<Rightarrow> Some True \<comment> \<open>if it has the trace, well and good\<close>
          | (Some False, None) \<Rightarrow>
             \<comment> \<open>the event wasn't there, but we may just not have checked far enough
                  - are there any other branches? \<close>
              (case (can_check_timestep, can_check_nondets) of
              \<comment> \<open>no other branches we can check - preserve False from event\<close>
              (None, None) \<Rightarrow> Some False
              \<comment> \<open>have other branches we can check, but they must have returned None\<close>
            | _ \<Rightarrow> None)
          | (Some x, Some y) => Some (disj x y)))"

end

fun filter_options :: "'a option list \<Rightarrow> 'a list" where
  "filter_options [] = []" |
  "filter_options (None # xs) = filter_options xs" |
  "filter_options (Some x # xs) = x # filter_options xs"

abbreviation "state_trace_of P timestep len branches t \<equiv> filter_options o fst o (StUpds_of P timestep len branches t)"


definition "cyphycircus_itree_trace_ref_by P Q t has_tick st0 \<equiv> (\<forall> x y timestep_den len branches.
  case (itree_has_trace x y (state_trace_of Q (1/timestep_den) len branches t st0) t has_tick
          (htree_of Q (1/timestep_den) \<one>\<^sub>L st0),
        itree_has_trace x y (state_trace_of P (1/timestep_den) len branches t st0) t has_tick
          (htree_of P (1/timestep_den) \<one>\<^sub>L st0)) of
      (Some a, Some b) \<Rightarrow> implies a b
    | _ \<Rightarrow> True
      )"

section \<open>testing the codegen\<close>

chantype foo =
  a :: nat                                    
  b :: unit

alphabet bar =
  n :: nat

record_default bar

lemma test1: "cyphycircus_itree_trace_ref_by (a\<^bold>.1 \<rightarrow> a\<^bold>.2 \<rightarrow>  Skip) (a\<^bold>.1 \<rightarrow> a\<^bold>.0 \<rightarrow> Skip) t has_tick (default::bar)"
  apply (unfold cyphycircus_itree_trace_ref_by_def cyphycircus_htree_defs, safe)
  quickcheck
  oops

recursive where "foo = b \<rightarrow> foo"

lemma test2: "cyphycircus_itree_trace_ref_by (b \<rightarrow> Skip) foo t has_tick (default::bar)"
  apply (unfold cyphycircus_htree_defs cyphycircus_itree_trace_ref_by_def
          foo_def foo_rec_fun_def, safe)
  quickcheck
  oops

lemma test3: "cyphycircus_itree_trace_ref_by foo (b \<rightarrow> Skip) t has_tick (default::bar)"
  apply (unfold cyphycircus_htree_defs cyphycircus_itree_trace_ref_by_def
          foo_def foo_rec_fun_def, safe)
  quickcheck
  oops
