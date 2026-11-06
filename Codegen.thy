theory Codegen
  imports Axiomatic_CyPhyCircus.Ax_CyPhyCircus
    "ITree_Simulation.Code_Target_Rational" Interaction_Trees.ITree_Extraction
    "HOL-Library.Multiset" "Framed_ODEs.Framed_ODEs"
    "HOL-Library.AList"
begin

unbundle Circus_Syntax
unbundle no UTP_Syntax
unbundle maplet_syntax

no_notation Abstract_Prog_Syntax.useq (infixr ";" 55)

section \<open>Miscellaneous Codegen Setup\<close>

lemma pfun_lookup_map_code [code]:
  "pfun_lookup (pfun_of_map f) k = f k"
  by auto

lemma integer_power_code[code]:
  "integer_power x n = (if n \<le> 0 then 1 else x * integer_power x (n-1))"
proof -
  obtain k :: nat where k_def: "k = nat_of_integer n"
    by blast
  then have k_minus_1_def: "n > 0 \<Longrightarrow> k-1 = nat_of_integer (n-1)"
    by (induct n, auto, metis Num.of_nat_simps(3) Suc_pred Zero_not_Suc cancel_ab_semigroup_add_class.add_diff_cancel_left'
        integer_of_int_eq_of_int nat_eq_iff2 nat_int nat_of_integer.abs_eq of_int_1 of_int_diff zero_less_nat_eq)
  have "x ^ k = (if k = 0 then 1 else x * x ^ (k-1))"
    by (induct k, auto)
  then show ?thesis
    unfolding integer_power_def 
    by (smt cr_integer_def eq_OO k_def k_minus_1_def less_eq_integer.rep_eq nat_of_integer.rep_eq
        nat_of_integer_non_positive not_le pcr_integer_def zero_integer.transfer zero_less_nat_eq)
qed

subsection \<open>Additional support for real numbers\<close>

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

lemma rat_of_int_code[code]: "Rat.of_int (int_of_integer n) = rat_of_rational (Frct_integer (n, 1))"
  by (simp add: rat_of_int_int_of_integer rational_of_integer_def)

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

(*ML \<open>val set_real_float_printings =
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
      in fold Code_Target.set_printings printings end\<close>*)

lemma inverse_rat_of_rational [code]: 
  "inverse (rat_of_rational x) = rat_of_rational (inverse x)"
  by (transfer, simp)

lemma integer_power_rat_of_rational [code]: 
  "integer_power (rat_of_rational x) n = rat_of_rational (integer_power x n)"
  unfolding integer_power_def by (transfer, simp)

lemma integer_power_Ratreal [code]: 
  "integer_power (Ratreal x) n = Ratreal (integer_power x n)"
  unfolding integer_power_def by (transfer, simp add: of_rat_power)

subsubsection \<open>Fixed-point real numbers\<close>

definition Scaled :: "integer \<Rightarrow> real" where
  "Scaled n = Real.real_of_int (int_of_integer n) / 1000000000"

definition round_Scaled :: "real \<Rightarrow> real" where
  "round_Scaled x = floor (x*1000000000) / 1000000000"

definition round_Scaled_integer :: "real \<Rightarrow> integer" where
  "round_Scaled_integer x = (THE n. Scaled n = floor (x*1000000000) / 1000000000)"

code_datatype Scaled Ratreal

lemma round_Scaled_Scaled[code]: "round_Scaled (Scaled n) = Scaled n"
  by (simp add: Scaled_def round_Scaled_def)

lemma round_Scaled_is_Scaled: "\<exists>!n. Scaled n = round_Scaled x"
  unfolding Scaled_def round_Scaled_def using integer_eqI int_of_integer_of_int by (auto, blast)

lemma round_Scaled_round_Scaled_integer_eq: "round_Scaled x = Scaled (round_Scaled_integer x)"
  by (smt (verit, ccfv_threshold) round_Scaled_def round_Scaled_integer_def round_Scaled_is_Scaled theI')

lemma round_Scaled_integer_Scaled[code]: "round_Scaled_integer (Scaled n) = n"
  by (simp add: Scaled_def round_Scaled_integer_def int_of_integer_inject)

lemma round_Scaled_Ratreal[code]:
  "round_Scaled (Ratreal x) = Scaled (integer_of_int (floor (x*1000000000)))"
  unfolding round_Scaled_def Scaled_def
  by (metis Ratreal_def int_of_integer_integer_of_int of_rat_numeral_eq real_floor_code real_times_code)

lemma round_Scaled_integer_Ratreal[code]:
  "round_Scaled_integer (Ratreal x) = integer_of_int (floor (x*1000000000))"
  by (metis round_Scaled_Ratreal round_Scaled_Scaled round_Scaled_def round_Scaled_integer_Scaled round_Scaled_integer_def)

lemma round_Scaled_idem: "round_Scaled (round_Scaled x) = round_Scaled x"
  by (simp add: round_Scaled_def)

lemma Scaled_plus[code]:
  "(Scaled x) + (Scaled y) = Scaled (x+y)"
  unfolding Scaled_def by auto

lemma Scaled_Ratreal_eq:
  "Scaled x = Ratreal (rat_of_rational (Frct_integer (x, 1000000000)))"
  unfolding Scaled_def
  by (metis Rat.of_int_def Ratreal_def divide_integer_rational divide_rational.rep_eq int_of_integer_numeral int_of_reals(6) of_rat_divide of_rat_of_int_eq
      rat_of_int_int_of_integer)

lemma Scaled_Ratreal_plus[code]:
  "(Scaled x) + (Ratreal y) = Ratreal (rat_of_rational (Frct_integer (x, 1000000000)) + y)"
  by (auto simp add: Scaled_Ratreal_eq real_plus_code of_rat_add)

lemma Ratreal_Scaled_plus[code]:
  "(Ratreal x) + (Scaled y) = Ratreal (x + rat_of_rational (Frct_integer (y, 1000000000)))"
  by (auto simp add: Scaled_Ratreal_eq real_plus_code of_rat_add)

lemma Scaled_minus[code]:
  "(Scaled x) - (Scaled y) = Scaled (x-y)"
  unfolding Scaled_def by auto

lemma Scaled_Ratreal_minus[code]:
  "(Scaled x) - (Ratreal y) = Ratreal (rat_of_rational (Frct_integer (x, 1000000000)) - y)"
  by (simp add: Scaled_Ratreal_eq of_rat_diff)

lemma Ratreal_Scaled_minus[code]:
  "(Ratreal x) - (Scaled y) = Ratreal (x - rat_of_rational (Frct_integer (y, 1000000000)))"
  by (simp add: Scaled_Ratreal_eq of_rat_diff)

lemma Scaled_uminus[code]:
  "-(Scaled x) = Scaled (-x)"
  unfolding Scaled_def by auto

lemmas [code del] = zero_real_code
lemma zero_real_code [code]:
  "(0 :: real) = Scaled 0"
  by (simp add: Scaled_def)

lemmas [code del] = one_real_code
lemma one_real_code [code]:
  "(1 :: real) = Scaled 1000000000"
  by (simp add: Scaled_def)

lemma Scaled_equal[code]:
  "HOL.equal (Scaled x) (Scaled y) \<longleftrightarrow> HOL.equal x y"
  unfolding Scaled_def by (auto simp add: equal_class.equal int_of_integer_inject)

lemma Scaled_Ratreal_equal[code]:
  "HOL.equal (Scaled x) (Ratreal y) \<longleftrightarrow> rat_of_rational (Frct_integer (x, 1000000000)) = y"
  by (auto simp add: equal_class.equal Scaled_Ratreal_eq)

lemma Ratreal_Scaled_equal[code]:
  "HOL.equal (Ratreal x) (Scaled y) \<longleftrightarrow> x = rat_of_rational (Frct_integer (y, 1000000000))"
  by (auto simp add: equal_class.equal Scaled_Ratreal_eq)

lemma Scaled_less[code]:
  "Scaled x < Scaled y \<longleftrightarrow> x < y"
  unfolding Scaled_def by (auto simp add: integer_less_iff)

lemma Scaled_Ratreal_less[code]:
  "Scaled x < Ratreal y \<longleftrightarrow> rat_of_rational (Frct_integer (x, 1000000000)) < y"
  by (auto simp add: Scaled_Ratreal_eq of_rat_less)

lemma Ratreal_Scaled_less[code]:
  "Ratreal x < Scaled y \<longleftrightarrow> x < rat_of_rational (Frct_integer (y, 1000000000))"
  by (simp add: Scaled_Ratreal_eq of_rat_less)

lemma Scaled_leq[code]:
  "Scaled x \<le> Scaled y \<longleftrightarrow> x \<le> y"
  unfolding Scaled_def by (auto simp add: integer_less_eq_iff)

lemma Scaled_Ratreal_leq[code]:
  "Scaled x \<le> Ratreal y \<longleftrightarrow> rat_of_rational (Frct_integer (x, 1000000000)) \<le> y"
  by (simp add: Scaled_Ratreal_eq of_rat_less_eq)

lemma Ratreal_Scaled_leq[code]:
  "Ratreal x \<le> Scaled y \<longleftrightarrow> x \<le> rat_of_rational (Frct_integer (y, 1000000000))"
  by (simp add: Scaled_Ratreal_eq of_rat_less_eq)

lemma Scaled_floor[code]:
  "floor (Scaled x) = int_of_integer (x div 1000000000)"
  unfolding Scaled_def
  by (metis divide_integer.rep_eq floor_divide_of_int_eq int_of_integer_numeral int_of_reals(6))

definition Scaled_mult :: "real \<Rightarrow> real \<Rightarrow> real" where
  "Scaled_mult x y = round_Scaled (x * y)"

lemma Scaled_mult_fold[code_unfold]:
  "round_Scaled (x * y) = Scaled_mult x y"
  unfolding Scaled_mult_def by auto

lemma Scaled_mult_Scaled[code]:
  "Scaled_mult (Scaled x) (Scaled y) = Scaled (x*y div 1000000000)"
  unfolding Scaled_mult_def round_Scaled_def Scaled_def by (auto, subst sym[OF floor_divide_of_int_eq], simp)

lemma Frct_integer_rep_eq:
  "x = Frct_integer (numerator x, denominator x)"
  unfolding Frct_integer_def numerator_def denominator_def
  using Fract_of_int_quotient quotient_of_div by auto

lemma Scaled_mult_Ratreal[code]:
  "Scaled_mult (Ratreal (rat_of_rational x)) (Ratreal (rat_of_rational y))
    = Scaled (((numerator x) * (numerator y) * 1000000000) div ((denominator x) * (denominator y)))"
  (is "?lhs = ?rhs")
proof -
  find_consts "rational \<Rightarrow> integer"
  have "?lhs = \<lfloor>Ratreal (rat_of_rational (Frct_integer ((numerator x), (denominator x))) * rat_of_rational (Frct_integer ((numerator y), (denominator y)))) * 1000000000\<rfloor> / 1000000000"
    unfolding Scaled_mult_def round_Scaled_def using Frct_integer_rep_eq real_times_code by (simp)
  also have "... = \<lfloor>Ratreal (rat_of_rational (Frct_integer ((numerator x), (denominator x)) * Frct_integer ((numerator y), (denominator y)))) * 1000000000\<rfloor> / 1000000000"
    using times_rational.rep_eq by presburger
  also have "... = \<lfloor>Ratreal (rat_of_rational (Frct_integer ((numerator x)*(numerator y), (denominator x)*(denominator y)))) * 1000000000\<rfloor> / 1000000000"
    by (smt Rat.of_int_def divide_divide_eq_left divide_divide_eq_right divide_integer_rational divide_rational.rep_eq
        of_int_mult rat_of_int_int_of_integer times_divide_eq_right times_integer.rep_eq)
  also have "... = \<lfloor>Ratreal (rat_of_rational (Frct_integer ((numerator x)*(numerator y)*1000000000, (denominator x)*(denominator y))))\<rfloor> / 1000000000"
    by (smt (verit, del_insts) Rat.of_int_def Scaled_def divide_integer_rational divide_rational.rep_eq int_of_integer_of_int int_of_reals(6) integer_of_int_eq_of_int
        rat_of_int_int_of_integer real_floor_code real_of_ints(4) round_Scaled_Ratreal round_Scaled_def times_divide_eq_left times_integer.rep_eq)
  also have "... = \<lfloor>Frct (int_of_integer ((numerator x)*(numerator y)*1000000000), int_of_integer ((denominator x)*(denominator y)))\<rfloor> / 1000000000"
    by (metis Fract_of_int_quotient Frct_def Rat.of_int_def divide_integer_rational divide_rational.rep_eq prod.sel(1,2)
        rat_of_int_int_of_integer real_floor_code)
  also have "... = (int_of_integer ((numerator x)*(numerator y)*1000000000) div int_of_integer ((denominator x)*(denominator y))) / 1000000000"
    by (metis Fract_of_int_quotient Frct_def floor_divide_of_int_eq prod.sel(1,2))
  also have "... = ?rhs"
    using Scaled_def divide_integer.rep_eq by presburger
  ultimately show ?thesis by auto
qed

lemma Scaled_mult_Scaled_Ratreal[code]:
  "Scaled_mult (Scaled x) (Ratreal (rat_of_rational y)) = Scaled ((x*numerator y) div denominator y)"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = real_of_int \<lfloor>real_of_int (int_of_integer x) * real_of_rat (rat_of_rational (Frct_integer (numerator y, denominator y)))\<rfloor> / 1000000000"
    unfolding Scaled_def Scaled_mult_def round_Scaled_def using Frct_integer_rep_eq by auto
  also have "... = real_of_int \<lfloor>real_of_rat (rat_of_rational (Frct_integer (x, 1))) * real_of_rat (rat_of_rational (Frct_integer (numerator y, denominator y)))\<rfloor> / 1000000000"
    by (metis Rat.of_int_def of_rat_of_int_eq rat_of_int_code)
  also have "... = real_of_int \<lfloor>real_of_rat (rat_of_rational (Frct_integer (x, 1)) * rat_of_rational (Frct_integer (numerator y, denominator y)))\<rfloor> / 1000000000"
    by (simp add: of_rat_mult)
  also have "... = real_of_int \<lfloor>real_of_rat (rat_of_rational (Frct_integer (x*numerator y, denominator y)))\<rfloor> / 1000000000"
    by (smt Rat.of_int_def divide_integer_rational divide_rational.rep_eq of_int_mult rat_of_int_code rat_of_int_int_of_integer times_divide_eq_right times_integer.rep_eq)
  also have "... = ?rhs"
    by (metis Rat.of_int_def Scaled_def divide_integer.rep_eq divide_integer_rational divide_rational.rep_eq floor_divide_of_int_eq of_rat_floor rat_of_int_int_of_integer)
  ultimately show ?thesis by auto
qed

lemma Scaled_mult_Ratreal_Scaled[code]:
  "Scaled_mult (Ratreal (rat_of_rational x)) (Scaled y) = Scaled ((numerator x*y) div denominator x)"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = real_of_int \<lfloor>real_of_rat (rat_of_rational (Frct_integer (numerator x, denominator x))) * real_of_int (int_of_integer y)\<rfloor> / 1000000000"
    unfolding Scaled_def Scaled_mult_def round_Scaled_def using Frct_integer_rep_eq by auto
  also have "... = real_of_int \<lfloor>real_of_rat (rat_of_rational (Frct_integer (numerator x, denominator x))) * real_of_rat (rat_of_rational (Frct_integer (y, 1)))\<rfloor> / 1000000000"
    by (metis Rat.of_int_def of_rat_of_int_eq rat_of_int_code)
  also have "... = real_of_int \<lfloor>real_of_rat (rat_of_rational (Frct_integer (numerator x, denominator x)) * rat_of_rational (Frct_integer (y, 1)))\<rfloor> / 1000000000"
    by (simp add: of_rat_mult)
  also have "... = real_of_int \<lfloor>real_of_rat (rat_of_rational (Frct_integer (numerator x * y, denominator x)))\<rfloor> / 1000000000"
    by (metis Groups.mult_ac(2) Rat.of_int_def Scaled_def Scaled_mult_Scaled_Ratreal Scaled_mult_def calculation divide_integer.rep_eq divide_integer_rational divide_rational.rep_eq
        floor_divide_of_int_eq of_rat_floor rat_of_int_int_of_integer)
  also have "... = ?rhs"
    by (metis Rat.of_int_def Scaled_def divide_integer.rep_eq divide_integer_rational divide_rational.rep_eq floor_divide_of_int_eq of_rat_floor rat_of_int_int_of_integer)
  ultimately show ?thesis by auto
qed

definition Scaled_div :: "real \<Rightarrow> real \<Rightarrow> real" where
  "Scaled_div x y = round_Scaled (x / y)"

lemma Scaled_div_fold[code_unfold]:
  "round_Scaled (x / y) = Scaled_div x y"
  unfolding Scaled_div_def by auto

lemma Scaled_div_Scaled[code]:
  "Scaled_div (Scaled x) (Scaled y) = Scaled ((x*1000000000) div y)"
  unfolding Scaled_div_def round_Scaled_def Scaled_def by (auto, subst sym[OF floor_divide_of_int_eq], simp)

lemma Scaled_div_Ratreal[code]:
  "Scaled_div (Ratreal (rat_of_rational x)) (Ratreal (rat_of_rational y)) = Scaled ((numerator x * denominator y * 1000000000) div (denominator x * numerator y))"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = round_Scaled (Ratreal (rat_of_rational (Frct_integer (numerator x, denominator x)) / rat_of_rational (Frct_integer (numerator y, denominator y))))"
    using Frct_integer_rep_eq Scaled_div_def real_divide_code by presburger
  also have "... = round_Scaled (Ratreal (rat_of_rational (Frct_integer (numerator x * denominator y, denominator x * numerator y))))"
    by (metis Rat.of_int_def divide_divide_times_eq divide_integer_rational divide_rational.rep_eq of_int_mult rat_of_int_int_of_integer times_integer.rep_eq)
  also have "... = real_of_int (int_of_integer ((numerator x * denominator y * 1000000000) div (denominator x * numerator y))) / 1000000000"
    by (smt (verit, ccfv_threshold) Rat.of_int_def Scaled_def divide_integer.rep_eq divide_integer_rational divide_rational.rep_eq floor_divide_of_int_eq int_of_integer_of_int
        int_of_reals(6) integer_of_int_eq_of_int of_int_mult rat_of_int_int_of_integer round_Scaled_Ratreal times_divide_eq_left times_integer.rep_eq)
  also have "... = ?rhs"
    by (simp add: Scaled_def)
  ultimately show ?thesis by auto
qed

lemma Scaled_div_Scaled_Ratreal[code]:
  "Scaled_div (Scaled x) (Ratreal (rat_of_rational y)) = Scaled ((x * denominator y) div numerator y)"
  by (smt (z3) Frct_integer_rep_eq Rat.of_int_def Scaled_Ratreal_eq Scaled_div_def divide_divide_eq_right divide_integer.rep_eq divide_integer_rational divide_rational.rep_eq
      eq_divide_eq_numeral1(1) floor_divide_of_int_eq int_of_integer_numeral int_of_reals(6) integer_of_int_eq_of_int of_int_integer_of of_int_mult rat_of_int_int_of_integer real_divide_code
      round_Scaled_Ratreal times_divide_eq_left times_integer.rep_eq)

lemma Scaled_div_Ratreal_Scaled[code]:
  "Scaled_div (Ratreal (rat_of_rational x)) (Scaled y) = Scaled ((numerator x * 1000000000 * 1000000000) div (denominator x * y))"
  by (smt (verit) Frct_integer_rep_eq Rat.of_int_def Scaled_Ratreal_eq Scaled_div_def divide_divide_times_eq divide_integer.rep_eq divide_integer_rational divide_rational.rep_eq
      floor_divide_of_int_eq int_of_integer_numeral int_of_reals(6) integer_of_int_eq_of_int of_int_integer_of of_int_mult rat_of_int_int_of_integer real_divide_code round_Scaled_Ratreal
      times_divide_eq_left times_integer.rep_eq)

lemma Scaled_div_inverse_fold[code_unfold]:
  "round_Scaled (inverse x) = Scaled_div 1 x"
  by (simp add: Scaled_div_def inverse_eq_divide)

lemma inverse_scaled[code]:
  "inverse (Scaled x) = Ratreal (rat_of_rational (Frct_integer (1000000000, x)))"
  by (metis Fract_of_int_quotient Rat.of_int_def Scaled_Ratreal_eq divide_integer_rational divide_rat_of_rational inverse_rat
      rat_of_int_int_of_integer real_inverse_code)
  

definition Scaled_int :: "int \<Rightarrow> real" where
  [code_unfold]: "Scaled_int n = Scaled (integer_of_int n*1000000000)"

definition Scaled_integer :: "integer \<Rightarrow> real" where
  [code_unfold]: "Scaled_integer n = Scaled (n*1000000000)"

lemma Scaled_int_of_int: "Scaled_int n = real_of_int n"
  unfolding Scaled_int_def Scaled_def by auto

lemma numeral_real_code [code]:
  "numeral k = Scaled (numeral k * 1000000000)"
  by (simp add: Scaled_def)

lemma of_int_real_code [code]:
  "of_int n = Scaled_int n"
  by (simp add: Scaled_int_def Scaled_def)

instantiation real :: default
begin

definition [code]: "default_real \<equiv> (Scaled_int 0)"

instance by intro_classes
end

lemma Ratreal_mult:
  "Ratreal (rat_of_rational (Frct_integer (x, y))) * Ratreal (rat_of_rational (Frct_integer (z, w)))
    = Ratreal (rat_of_rational (Frct_integer (x * z, y*w)))"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = Ratreal ((rat_of_rational (Frct_integer (x, y))) * (rat_of_rational (Frct_integer (z, w))))"
    using real_times_code by presburger
  also have "... = Ratreal (rat_of_rational (Frct_integer (x, y) * Frct_integer (z, w)))"
    by simp
  also have "... = ?rhs"
    by (smt (verit, del_insts) Fract_of_int_quotient Rat.of_int_def divide_integer_rational divide_rational.rep_eq mult_rat
        rat_of_int_int_of_integer times_integer.rep_eq times_rational.rep_eq)
  ultimately show ?thesis by auto
qed
  
lemma Scaled_mult[code]:
  "(Scaled x) * (Scaled y) = Ratreal (rat_of_rational (Frct_integer (x * y, 1000000000000000000)))"
  unfolding Scaled_Ratreal_eq by (subst Ratreal_mult, simp)


lemma Scaled_Ratreal_mult[code]:
  "(Scaled x) * (Ratreal y) = Ratreal (rat_of_rational (Frct_integer (x, 1000000000)) * y)"
  by (auto simp add: Scaled_Ratreal_eq real_times_code of_rat_mult)

lemma Ratreal_Scaled_mult[code]:
  "(Ratreal x) * (Scaled y) = Ratreal (x * rat_of_rational (Frct_integer (y, 1000000000)))"
  by (auto simp add: Scaled_Ratreal_eq real_times_code of_rat_mult)

lemma Ratreal_div:
  "Ratreal (rat_of_rational (Frct_integer (x, y))) / Ratreal (rat_of_rational (Frct_integer (z, w)))
    = Ratreal (rat_of_rational (Frct_integer (x * w, y * z)))"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = Ratreal ((rat_of_rational (Frct_integer (x, y))) / (rat_of_rational (Frct_integer (z, w))))"
    using real_divide_code by presburger
  also have "... = Ratreal (rat_of_rational (Frct_integer (x, y) / Frct_integer (z, w)))"
    by (simp add: divide_rational.rep_eq)
  also have "... = ?rhs"
    by (metis Ratreal_mult divide_divide_eq_right divide_integer_rational real_times_code times_divide_eq_right
        times_rat_of_rational)
  ultimately show ?thesis by auto
qed
  
lemma Scaled_div[code]:
  "(Scaled x) / (Scaled y) = Ratreal (rat_of_rational (Frct_integer (x, y)))"
  unfolding Scaled_Ratreal_eq
  by (smt (verit, ccfv_threshold) Rat.of_int_def divide_divide_eq_right divide_integer_rational divide_rational.rep_eq
      eq_divide_eq_numeral1(1) int_of_integer_of_int int_of_reals(6) rat_of_int_int_of_integer real_divide_code
      semiring_norm(143))

lemma Scaled_Ratreal_div[code]:
  "(Scaled x) / (Ratreal y) = Ratreal (rat_of_rational (Frct_integer (x, 1000000000)) / y)"
  by (auto simp add: Scaled_Ratreal_eq real_divide_code of_rat_divide)

lemma Ratreal_Scaled_div[code]:
  "(Ratreal x) / (Scaled y) = Ratreal (x / rat_of_rational (Frct_integer (y, 1000000000)))"
  by (auto simp add: Scaled_Ratreal_eq real_divide_code of_rat_divide)

code_printing
  constant "Code_Evaluation.term_of :: real \<Rightarrow> term" \<rightharpoonup>
    (SML) "(fn x =>
              case x of
                  Scaled n => 
                     let val d = Integer.gcd n 1000000000
                         val num = HOLogic.mk'_number HOLogic.realT (n div d)
                         val den = HOLogic.mk'_number HOLogic.realT (1000000000 div d)
                     in Const (\"Rings.divide'_class.divide\", HOLogic.realT --> HOLogic.realT --> HOLogic.realT) $ num $ den end
                | Ratreal (Rat'_of'_rational r) =>
                    let val num = HOLogic.mk'_number integerT (fst (Rat.dest r))
                        val den = HOLogic.mk'_number integerT (snd (Rat.dest r))
                        val pair = HOLogic.mk'_prod (num, den)
                    in Const (\"Code'_Rational.Frct'_integer\",(HOLogic.mk'_prodT (integerT, integerT)) --> rationalT) $ pair
                    end)"
  | constant "Real.term_of_real_inst.term_of_real" \<rightharpoonup>
    (SML) "(fn x =>
              case x of
                  Scaled n => 
                     let val d = Integer.gcd n 1000000000
                         val num = HOLogic.mk'_number HOLogic.realT (n div d)
                         val den = HOLogic.mk'_number HOLogic.realT (1000000000 div d)
                     in Const (\"Rings.divide'_class.divide\", HOLogic.realT --> HOLogic.realT --> HOLogic.realT) $ num $ den end
                | Ratreal (Rat'_of'_rational r) =>
                    let val num = HOLogic.mk'_number integerT (fst (Rat.dest r))
                        val den = HOLogic.mk'_number integerT (snd (Rat.dest r))
                        val pair = HOLogic.mk'_prod (num, den)
                    in Const (\"Code'_Rational.Frct'_integer\",(HOLogic.mk'_prodT (integerT, integerT)) --> rationalT) $ pair
                    end)"

subsection \<open>Additional support for sets and channel sets\<close>

definition set_to_list :: "'a set \<Rightarrow> 'a list option" where
  [code del]: "set_to_list S = (if \<exists>xs. S = List.set xs then Some (SOME xs. S = List.set xs) else None)"

lemma set_to_list_sound:
  "set_to_list S = Some xs \<Longrightarrow> set xs = S"
  unfolding set_to_list_def by (auto simp add: verit_sko_ex)

lemma set_to_list_infinite:
  "\<not> finite S \<Longrightarrow> set_to_list S = None"
  unfolding set_to_list_def by auto

code_printing constant set_to_list => (SML) "(fn Set xs => SOME (Library.distinct (=) xs) | '_ => NONE)"

definition csbasic2 :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> 'e set" where
[code_unfold]: "csbasic2 c = Collect (Not o Option.is_none o match\<^bsub>c\<^esub>)"

definition csinsert2 :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> 'e set \<Rightarrow> 'e set" where
[code_unfold]: "csinsert2 e E = csbasic2 e \<union> E"

syntax 
  "_ch_enum_func"       :: "chans \<Rightarrow> logic" ("\<lbrace>_\<rbrace>\<^sub>f")

translations
  "_ch_enum_func (_chan c)" \<rightleftharpoons> "CONST csbasic2 c"
  "_ch_enum_func (_chans c cs)" \<rightleftharpoons> "CONST csinsert2 c (_ch_enum_func cs)"

lemma csbasic_csbasic2_eq:
  assumes "wb_prism c"
  shows "csbasic c = csbasic2 c"
  unfolding csbasic_def csbasic2_def by (auto simp add: assms Option.is_none_def domIff wb_prism.range_build)

lemma csinsert_cs_insert2_eq:
  assumes "wb_prism c"
  shows "csinsert c S = csinsert2 c S"
  unfolding csinsert_def csinsert2_def by (auto simp add: assms csbasic_csbasic2_eq)

code_datatype Collect List.set List.coset
lemmas [code del] = sym[OF Set.Collect_disj_eq]

unbundle no UTP_Syntax

definition pred_or :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)" where
  "pred_or f g = (\<lambda>x. f x \<or> g x)"

lemma pred_or_code [code]:
  "pred_or f g x \<longleftrightarrow> f x \<or> g x"
  by (simp add: pred_or_def)

lemma union_Collect_code[code]:
  "(Collect f) \<union> (Collect g) = Collect (pred_or f g)"
  unfolding pred_or_def by blast

lemmas [code] = mem_Collect_eq insert_Collect

subsection \<open>Definitions to force monomorphisation\<close>

definition fast_member :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" where
  "fast_member x S \<longleftrightarrow> x \<in> S"

declare [[code drop: fast_member]]

code_printing
  constant fast_member \<rightharpoonup> (SML) 
    "case (_, _) of
        (x, Coset xs) => not (Library.member (=) xs x)
      | (x, Set xs) => Library.member (=) xs x
      | (x, Collect f) => f x"

definition fast_equal :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "fast_equal x y \<longleftrightarrow> (x = y)"

declare [[code drop: fast_equal]]

code_printing
  constant fast_equal \<rightharpoonup> (SML) "((_) = (_))"
  and (Haskell) "((_) == (_))"
  and (Scala) "((_) == (_))"

lemmas [[code drop: list_ex1]]

ML \<open>fun list_ex1 p (x :: xs) =
          (if p x then List.all (fn y => not (p y) orelse x = y) xs
            else list_ex1 p xs)
      | list_ex1 p [] = false;\<close>

code_printing
  constant list_ex1 \<rightharpoonup> (SML) "list'_ex1"

lemmas [[code drop: List.member]]

code_printing
  constant List.member \<rightharpoonup> (SML) "Library.member (=)"
ML "Library.member"

section \<open>cyphyaction as a code_datatype\<close>

subsection \<open>Approximate solutions to differential equations (to remove a type parameter from the code datatype)\<close>

class round_vector = real_normed_vector +
  fixes round_vec :: "'a \<Rightarrow> 'a"
  fixes scaleR_round :: "real \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes round_vec_idempotent [simp]: "round_vec (round_vec x) = round_vec x"
  assumes scaleR_round_round_vec [simp]: "round_vec (y *\<^sub>R x) = scaleR_round y x"

instantiation real :: round_vector
begin
  definition round_vec_real :: "real \<Rightarrow> real" where
    "round_vec_real = round_Scaled"
  definition scaleR_round_real :: "real \<Rightarrow> real \<Rightarrow> real" where
    "scaleR_round_real = Scaled_mult"

  instance proof
    fix x y :: real
    show "round_vec (round_vec x) = round_vec x"
      unfolding round_vec_real_def by (simp add: round_Scaled_idem)
    show "round_vec (y *\<^sub>R x) = scaleR_round y x"
      unfolding round_vec_real_def scaleR_round_real_def Scaled_mult_def by auto
  qed
end

instantiation prod :: (round_vector, round_vector) round_vector
begin
  definition round_vec_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b" where
    "round_vec_prod v = (round_vec (fst v), round_vec (snd v))"
  definition scaleR_round_prod :: "real \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b" where
    "scaleR_round_prod x p = (scaleR_round x (fst p), scaleR_round x (snd p))"

  instance proof
    fix x :: "'a \<times> 'b"
    fix y :: real
    show "round_vec (round_vec x) = round_vec x"
      unfolding round_vec_prod_def by simp
    show "round_vec (y *\<^sub>R x) = scaleR_round y x"
      unfolding round_vec_prod_def scaleR_round_prod_def Scaled_mult_def by auto
  qed
end

lemma round_vec_prod [code_unfold]:
  "round_vec (a, b) = (round_vec a, round_vec b)"
  by (simp add: round_vec_prod_def)

lemma scaleR_round_prod [code_unfold]:
  "scaleR_round x (a, b) = (scaleR_round x a, scaleR_round x b)"
  by (simp add: scaleR_round_prod_def)

lemma scaleR_round_real [code_unfold]:
  "scaleR_round x y = Scaled_mult x y"
  by (simp add: scaleR_round_real_def)

lemma round_vec_real [code_unfold]:
  "round_vec (x::real) = round_Scaled x"
  by (simp add: round_vec_real_def)

lemma plus_prod_code [code]:
  "(a, b) + (c, d) = (a + c, b + d)"
  by auto

lemma scaleR_prod_code [code]:
  "r *\<^sub>R (a, b) = (r *\<^sub>R a, r *\<^sub>R b)"
  by auto

definition "RKstep_round_k2_k3_input h y k1k2 = y + (scaleR_round (Scaled_div h (Scaled 2000000000)) k1k2)"

definition "RKstep_round_k4_input h y k4 = y + (scaleR_round h k4)"

definition "RKstep_round_output y h k1 k2 k3 k4
  = y + (scaleR_round (Scaled_div h (Scaled 6000000000)) (k1 + (scaleR_round (Scaled 2000000000) k2) + (scaleR_round (Scaled 2000000000) k3) + k4))"

abbreviation "RKstep f h y \<equiv>
  let k1 = f y;
      k2 = f (y + ((h / 2) *\<^sub>R k1));
      k3 = f (y + ((h / 2) *\<^sub>R k2));
      k4 = f (y + h *\<^sub>R k3)
  in y + (h / 6) *\<^sub>R (k1 + 2*\<^sub>Rk2 + 2*\<^sub>Rk3 + k4)"

definition "RKstep_round f h y \<equiv>
  let h' = round_Scaled h;
      h2 = Scaled_div h' (Scaled 2000000000);
      h6 = Scaled_div h' (Scaled 6000000000);
      y' = round_vec y;
      f' = round_vec \<circ> f;
      k1 = f' y';
      k2 = f' (y' + (scaleR_round h2 k1));
      k3 = f' (y' + (scaleR_round h2 k2));
      k4 = f' (y' + (scaleR_round h' k3))
  in y' + (scaleR_round h6 (k1 + (scaleR_round (Scaled 2000000000) k2) + (scaleR_round (Scaled 2000000000) k3) + k4))"

lemma RKstep_round_def2:
  "RKstep_round f h y \<equiv>
    let h' = round_Scaled h;
      y' = round_vec y;
      f' = round_vec \<circ> f;
      k1 = f' y';
      k2 = f' (RKstep_round_k2_k3_input h' y' k1);
      k3 = f' (RKstep_round_k2_k3_input h' y' k2);
      k4 = f' (RKstep_round_k4_input h' y' k3)
    in RKstep_round_output y' h' k1 k2 k3 k4"
  unfolding RKstep_round_def RKstep_round_k2_k3_input_def RKstep_round_k4_input_def RKstep_round_output_def
  by (auto, smt (verit, best))

lemmas [code del] = RKstep_round_def
lemmas [code] = RKstep_round_def2

subsubsection \<open>Monomorphisation for a single real number\<close>

definition "RKstep_round_k2_k3_input_real h y k1k2 = y + (Scaled_mult (Scaled_div h (Scaled 2000000000)) k1k2)"

definition "RKstep_round_k4_input_real h y k4 = y + (Scaled_mult h k4)"

definition "RKstep_round_output_real y h k1 k2 k3 k4
  = y + (Scaled_mult (Scaled_div h (Scaled 6000000000)) (k1 + (Scaled_mult (Scaled 2000000000) k2) + (Scaled_mult (Scaled 2000000000) k3) + k4))"

lemma RKstep_round_k2_k3_input_real_Scaled[code]:
  "RKstep_round_k2_k3_input_real (Scaled h) (Scaled y) (Scaled k1k2) = Scaled (y + ((k1k2*(h div 2)) div 1000000000))"
  unfolding RKstep_round_k2_k3_input_real_def Scaled_div_Scaled Scaled_mult_Scaled Scaled_plus
  by (auto simp add: cross3_simps(11))

lemma RKstep_round_k4_input_real_Scaled[code]:
  "RKstep_round_k4_input_real (Scaled h) (Scaled y) (Scaled k3) = Scaled (y + (h * k3) div 1000000000)"
  unfolding RKstep_round_k4_input_real_def scaleR_round_real Scaled_mult_Scaled Scaled_plus by auto

lemma RKstep_round_output_real_Scaled[code]:
  "RKstep_round_output_real (Scaled y) (Scaled h) (Scaled k1) (Scaled k2) (Scaled k3) (Scaled k4)
    = Scaled (y + ((h div 6) * (k1 + (2 * k2) + (2 * k3) + k4)) div 1000000000)"
  unfolding RKstep_round_output_real_def Scaled_div_Scaled scaleR_round_real Scaled_mult_Scaled Scaled_plus
  by auto

lemma RKstep_round_k2_k3_input_real_eq[code_unfold]:
  "RKstep_round_k2_k3_input = RKstep_round_k2_k3_input_real"
  by (auto simp add: ext RKstep_round_k2_k3_input_def RKstep_round_k2_k3_input_real_def scaleR_round_real)

lemma RKstep_round_k4_input_real_eq[code_unfold]:
  "RKstep_round_k4_input = RKstep_round_k4_input_real"
  by (auto simp add: ext RKstep_round_k4_input_def RKstep_round_k4_input_real_def scaleR_round_real)


lemma RKstep_round_output_real_eq[code_unfold]:
  "RKstep_round_output = RKstep_round_output_real"
  by (auto simp add: ext RKstep_round_output_def RKstep_round_output_real_def scaleR_round_real)

definition
  "RKstep_round_real f h y \<equiv>
    let h' = round_Scaled h;
      y' = round_Scaled y;
      f' = round_Scaled \<circ> f;
      k1 = f' y';
      k2 = f' (RKstep_round_k2_k3_input_real h' y' k1);
      k3 = f' (RKstep_round_k2_k3_input_real h' y' k2);
      k4 = f' (RKstep_round_k4_input_real h' y' k3)
    in RKstep_round_output_real y' h' k1 k2 k3 k4"

lemma RKstep_round_real_eq[code_unfold]:
  "RKstep_round = RKstep_round_real"
  by (intro ext, simp add: RKstep_round_def2 RKstep_round_k2_k3_input_real_eq RKstep_round_k4_input_real_eq RKstep_round_output_real_eq RKstep_round_real_def round_vec_real)

subsubsection \<open>Monomorphisation for different tuple sizes\<close>

ML \<open>fun RKstep_round_k2_k3_input_tuple_defn_term n = 
      let val hs = map (fn _ => Free ("h", HOLogic.realT)) (Library.upto (1,n))
          val ys = map (fn i => Free ("y" ^ Int.toString i, HOLogic.realT)) (Library.upto (1,n))
          val k1k2s = map (fn i => Free ("k1k2_" ^ Int.toString i, HOLogic.realT)) (Library.upto (1,n))
          fun RKstep_round_k2_k3_input_real (h, (y, k1k2)) = @{term RKstep_round_k2_k3_input_real} $ h $ y $ k1k2
          val output_tuple_terms = map RKstep_round_k2_k3_input_real (ListPair.zip (hs, ListPair.zip (ys, k1k2s)))
          val rhs = HOLogic.mk_tuple output_tuple_terms
          val y_tuple = HOLogic.mk_tuple ys
          val k1k2_tuple = HOLogic.mk_tuple k1k2s
          val tuple_type = HOLogic.mk_tupleT (map (fn _ => HOLogic.realT) (Library.upto (1,n)))
          val RKstep_round_k2_k3_input_tuple_term = Free ("RKstep_round_k2_k3_input_tuple" ^ Int.toString n, HOLogic.realT --> tuple_type --> tuple_type --> tuple_type)
          val lhs = RKstep_round_k2_k3_input_tuple_term $ (Free ("h", HOLogic.realT)) $ y_tuple $ k1k2_tuple
      in @{term Trueprop} $ (Const (@{const_name HOL.eq}, tuple_type --> tuple_type --> HOLogic.boolT) $ lhs $ rhs)
      end\<close>
ML \<open>fun make_RKstep_round_k2_k3_input_tuple_defn n ctxt =
      let val decl = (Binding.make ("RKstep_round_k2_k3_input_tuple" ^ Int.toString n, @{here}), NONE, NoSyn)
          val spec = ((Binding.empty_atts, RKstep_round_k2_k3_input_tuple_defn_term n), [], [])
      in Function_Fun.add_fun [decl] [spec] Function_Fun.fun_config ctxt
      end\<close>

ML \<open>fun RKstep_round_k4_input_tuple_defn_term n = 
      let val hs = map (fn _ => Free ("h", HOLogic.realT)) (Library.upto (1,n))
          val ys = map (fn i => Free ("y" ^ Int.toString i, HOLogic.realT)) (Library.upto (1,n))
          val k3s = map (fn i => Free ("k3_" ^ Int.toString i, HOLogic.realT)) (Library.upto (1,n))
          fun RKstep_round_k4_input_real (h, (y, k3)) = @{term RKstep_round_k4_input_real} $ h $ y $ k3
          val output_tuple_terms = map RKstep_round_k4_input_real (ListPair.zip (hs, ListPair.zip (ys, k3s)))
          val rhs = HOLogic.mk_tuple output_tuple_terms
          val y_tuple = HOLogic.mk_tuple ys
          val k3_tuple = HOLogic.mk_tuple k3s
          val tuple_type = HOLogic.mk_tupleT (map (fn _ => HOLogic.realT) (Library.upto (1,n)))
          val RKstep_round_k4_input_tuple_term = Free ("RKstep_round_k4_input_tuple" ^ Int.toString n, HOLogic.realT --> tuple_type --> tuple_type --> tuple_type)
          val lhs = RKstep_round_k4_input_tuple_term $ (Free ("h", HOLogic.realT)) $ y_tuple $ k3_tuple
      in @{term Trueprop} $ (Const (@{const_name HOL.eq}, tuple_type --> tuple_type --> HOLogic.boolT) $ lhs $ rhs)
      end\<close>
ML \<open>fun make_RKstep_round_k4_input_tuple_defn n ctxt =
      let val decl = (Binding.make ("RKstep_round_k4_input_tuple" ^ Int.toString n, @{here}), NONE, NoSyn)
          val spec = ((Binding.empty_atts, RKstep_round_k4_input_tuple_defn_term n), [], [])
      in Function_Fun.add_fun [decl] [spec] Function_Fun.fun_config ctxt
      end\<close>

ML \<open>fun RKstep_round_output_tuple_defn_term n = 
      let val hs = map (fn _ => Free ("h", HOLogic.realT)) (Library.upto (1,n))
          val ys = map (fn i => Free ("y" ^ Int.toString i, HOLogic.realT)) (Library.upto (1,n))
          val k1s = map (fn i => Free ("k1_" ^ Int.toString i, HOLogic.realT)) (Library.upto (1,n))
          val k2s = map (fn i => Free ("k2_" ^ Int.toString i, HOLogic.realT)) (Library.upto (1,n))
          val k3s = map (fn i => Free ("k3_" ^ Int.toString i, HOLogic.realT)) (Library.upto (1,n))
          val k4s = map (fn i => Free ("k4_" ^ Int.toString i, HOLogic.realT)) (Library.upto (1,n))
          fun RKstep_round_output_real (y, (h, (k1, (k2, (k3, k4))))) = @{term RKstep_round_output_real} $ y $ h $ k1 $ k2 $ k3 $ k4
          val output_tuple_terms = map RKstep_round_output_real (ListPair.zip (ys, ListPair.zip (hs, ListPair.zip (k1s, ListPair.zip (k2s, ListPair.zip (k3s, k4s))))))
          val rhs = HOLogic.mk_tuple output_tuple_terms
          val y_tuple = HOLogic.mk_tuple ys
          val k1_tuple = HOLogic.mk_tuple k1s
          val k2_tuple = HOLogic.mk_tuple k2s
          val k3_tuple = HOLogic.mk_tuple k3s
          val k4_tuple = HOLogic.mk_tuple k4s
          val tuple_type = HOLogic.mk_tupleT (map (fn _ => HOLogic.realT) (Library.upto (1,n)))
          val typ = tuple_type --> HOLogic.realT --> tuple_type --> tuple_type --> tuple_type --> tuple_type --> tuple_type
          val RKstep_round_output_tuple_term = Free ("RKstep_round_output_tuple" ^ Int.toString n, typ)
          val lhs = RKstep_round_output_tuple_term $ y_tuple $ (Free ("h", HOLogic.realT)) $ k1_tuple $ k2_tuple $ k3_tuple $ k4_tuple
      in @{term Trueprop} $ (Const (@{const_name HOL.eq}, tuple_type --> tuple_type --> HOLogic.boolT) $ lhs $ rhs)
      end\<close>
ML \<open>fun make_RKstep_round_output_tuple_defn n ctxt =
      let val decl = (Binding.make ("RKstep_round_output_tuple" ^ Int.toString n, @{here}), NONE, NoSyn)
          val spec = ((Binding.empty_atts, RKstep_round_output_tuple_defn_term n), [], [])
      in Function_Fun.add_fun [decl] [spec] Function_Fun.fun_config ctxt
      end\<close>

ML \<open>fun make_round_vec_tuple_defn n ctxt =
      let val decl = (Binding.make ("round_vec_tuple" ^ Int.toString n, @{here}), NONE, NoSyn)
          val xs = map (fn i => Free ("x" ^ Int.toString i, HOLogic.realT)) (Library.upto (1,n))
          val rhs = HOLogic.mk_tuple (map (fn t => @{term round_Scaled} $ t) xs)
          val x_tuple = HOLogic.mk_tuple xs
          val tuple_type = HOLogic.mk_tupleT (map (fn _ => HOLogic.realT) (Library.upto (1,n)))
          val lhs = Free ("round_vec_tuple" ^ Int.toString n, tuple_type --> tuple_type) $ x_tuple
          val term = @{term Trueprop} $ (Const (@{const_name HOL.eq}, tuple_type --> tuple_type --> HOLogic.boolT) $ lhs $ rhs)
          val spec = ((Binding.empty_atts, term), [], [])
      in Function_Fun.add_fun [decl] [spec] Function_Fun.fun_config ctxt
      end\<close>

ML \<open>fun make_RKstep_round_tuple_defn n ctxt =
      let val tuple_type = HOLogic.mk_tupleT (map (fn _ => HOLogic.realT) (Library.upto (1,n)))
          val RKstep_round_output = Proof_Context.read_const {proper=true, strict=true} ctxt ("RKstep_round_output_tuple" ^ Int.toString n)
          val output_term = RKstep_round_output $ Bound 5 $ Bound 6 $ Bound 3 $ Bound 2 $ Bound 1 $ Bound 0
          val k4_abs_term = Abs ("k4", tuple_type, output_term)
          val RKstep_round_k4_input = Proof_Context.read_const {proper=true, strict=true} ctxt ("RKstep_round_k4_input_tuple" ^ Int.toString n)
          val k4_term = (Bound 3 $ (RKstep_round_k4_input $ Bound 5 $ Bound 4 $ Bound 0))
          val k4_let_term = Const ("HOL.Let", tuple_type --> (tuple_type --> tuple_type) --> tuple_type) $ k4_term $ k4_abs_term
          val k3_abs_term = Abs ("k3", tuple_type, k4_let_term)
          val RKstep_round_k2_k3_input = Proof_Context.read_const {proper=true, strict=true} ctxt ("RKstep_round_k2_k3_input_tuple" ^ Int.toString n)
          val k3_term = (Bound 2 $ (RKstep_round_k2_k3_input $ Bound 4 $ Bound 3 $ Bound 0))
          val k3_let_term = Const ("HOL.Let", tuple_type --> (tuple_type --> tuple_type) --> tuple_type) $ k3_term $ k3_abs_term
          val k2_abs_term = Abs ("k2", tuple_type, k3_let_term)
          val k2_term = (Bound 1 $ (RKstep_round_k2_k3_input $ Bound 3 $ Bound 2 $ Bound 0))
          val k2_let_term = Const ("HOL.Let", tuple_type --> (tuple_type --> tuple_type) --> tuple_type) $ k2_term $ k2_abs_term
          val k1_abs_term = Abs ("k1", tuple_type, k2_let_term)
          val k1_term = (Bound 0 $ Bound 1)
          val k1_let_term = Const ("HOL.Let", tuple_type --> (tuple_type --> tuple_type) --> tuple_type) $ k1_term $ k1_abs_term
          val f'_abs_term = Abs ("f'", tuple_type --> tuple_type, k1_let_term)
          val round_vec = Proof_Context.read_const {proper=true, strict=true} ctxt ("round_vec_tuple" ^ Int.toString n)
          val f'_term = (Const ("Fun.comp", (tuple_type --> tuple_type) --> (tuple_type --> tuple_type) --> tuple_type --> tuple_type) $ round_vec $ Free ("f", tuple_type --> tuple_type))
          val f'_let_term = Const ("HOL.Let", (tuple_type --> tuple_type) --> ((tuple_type --> tuple_type) --> tuple_type) --> tuple_type) $ f'_term $ f'_abs_term
          val y'_abs_term = Abs ("y'", tuple_type, f'_let_term)
          val y'_term = (round_vec $ Free ("y", tuple_type))
          val y'_let_term = Const ("HOL.Let", tuple_type --> (tuple_type --> tuple_type) --> tuple_type) $ y'_term $ y'_abs_term
          val h'_abs_term = Abs ("h'", HOLogic.realT, y'_let_term)
          val h'_term = (@{term round_Scaled} $ Free ("h", HOLogic.realT))
          val h'_let_term = Const ("HOL.Let", HOLogic.realT --> (HOLogic.realT --> tuple_type) --> tuple_type) $ h'_term $ h'_abs_term
          val rhs = h'_let_term
          val typ = (tuple_type --> tuple_type) --> HOLogic.realT --> tuple_type --> tuple_type
          val RKstep_round_tuple_term = Free ("RKstep_round_tuple" ^ Int.toString n, typ)
          val lhs = RKstep_round_tuple_term $ (Free ("f", tuple_type --> tuple_type)) $ (Free ("h", HOLogic.realT)) $ (Free ("y", tuple_type))
          val term = @{term Trueprop} $ (Const (@{const_name HOL.eq}, tuple_type --> tuple_type --> HOLogic.boolT) $ lhs $ rhs)
          val decl = (Binding.make ("RKstep_round_tuple" ^ Int.toString n, @{here}), NONE, NoSyn)
          val spec = (Binding.empty_atts, term)
      in Specification.definition (SOME decl) [] [] spec ctxt
      end\<close>

ML \<open>fun make_RKstep_round_tuple_defns n ctxt =
      ctxt
        |> make_RKstep_round_k2_k3_input_tuple_defn n
        |> make_RKstep_round_k4_input_tuple_defn n
        |> make_RKstep_round_output_tuple_defn n
        |> make_round_vec_tuple_defn n
        |> snd o (make_RKstep_round_tuple_defn n)\<close>

lemma RKstep_round_k2_k3_input_prod: "RKstep_round_k2_k3_input h (y1, y2) (k1k2_1, k1k2_2) = (RKstep_round_k2_k3_input h y1 k1k2_1, RKstep_round_k2_k3_input h y2 k1k2_2)"
  by (simp add: RKstep_round_k2_k3_input_def scaleR_round_prod_def)

lemma RKstep_round_k4_input_prod: "RKstep_round_k4_input h (y1, y2) (k1k2_1, k1k2_2) = (RKstep_round_k4_input h y1 k1k2_1, RKstep_round_k4_input h y2 k1k2_2)"
  by (simp add: RKstep_round_k4_input_def scaleR_round_prod_def)

lemma RKstep_round_output_prod: "RKstep_round_output (y1, y2) h (k1_1, k1_2) (k2_1, k2_2) (k3_1, k3_2) (k4_1, k4_2)
    = (RKstep_round_output y1 h k1_1 k2_1 k3_1 k4_1, RKstep_round_output y2 h k1_2 k2_2 k3_2 k4_2)"
  by (simp add: RKstep_round_output_def scaleR_round_prod_def)

ML \<open>fun read_method ctxt str =
      let val keywords = Thy_Header.get_keywords' ctxt
          val src = Token.explode0 keywords str |> filter Token.is_proper
          val text = Method.read ctxt src
      in Method.evaluate text ctxt
      end\<close>

ML \<open>fun prove_RKstep_round_k2_k3_input_tuple_unfolding n ctxt =
      let val tuple_type = HOLogic.mk_tupleT (map (fn _ => HOLogic.realT) (Library.upto (1,n)))
          val typ = HOLogic.realT --> tuple_type --> tuple_type --> tuple_type
          val RKstep_round_k2_k3_input = Const (@{const_name RKstep_round_k2_k3_input}, typ)
          val RKstep_round_k2_k3_input_tuple = Proof_Context.read_const {proper=true, strict=true} ctxt ("RKstep_round_k2_k3_input_tuple" ^ Int.toString n)
          val term = @{term Trueprop} $ (Const (@{const_name HOL.eq}, typ --> typ --> HOLogic.boolT) $ RKstep_round_k2_k3_input $ RKstep_round_k2_k3_input_tuple)
          val goal = Goal.init (Thm.cterm_of ctxt term)
          val method = read_method ctxt "(intro ext, auto simp add: RKstep_round_k2_k3_input_prod RKstep_round_k2_k3_input_real_eq)"
          val (ctxt, goal) = Seq.the_result ("RKstep_round_k2_k3_input_tuple" ^ Int.toString n ^ "unfolding proof failed") (method [] (ctxt, goal))
          val thm = Goal.finish ctxt goal
          val name = Binding.name ("RKstep_round_k2_k3_input_tuple" ^ Int.toString n ^ "_unfold")
          val binding : Attrib.binding = (name, @{attributes [code_unfold]})
          val (_, ctxt) = Local_Theory.note (binding, [thm]) ctxt
      in ctxt
      end\<close>

ML \<open>fun prove_RKstep_round_k4_input_tuple_unfolding n ctxt =
      let val tuple_type = HOLogic.mk_tupleT (map (fn _ => HOLogic.realT) (Library.upto (1,n)))
          val typ = HOLogic.realT --> tuple_type --> tuple_type --> tuple_type
          val RKstep_round_k4_input = Const (@{const_name RKstep_round_k4_input}, typ)
          val RKstep_round_k4_input_tuple = Proof_Context.read_const {proper=true, strict=true} ctxt ("RKstep_round_k4_input_tuple" ^ Int.toString n)
          val term = @{term Trueprop} $ (Const (@{const_name HOL.eq}, typ --> typ --> HOLogic.boolT) $ RKstep_round_k4_input $ RKstep_round_k4_input_tuple)
          val goal = Goal.init (Thm.cterm_of ctxt term)
          val method = read_method ctxt "(intro ext, auto simp add: RKstep_round_k4_input_prod RKstep_round_k4_input_real_eq)"
          val (ctxt, goal) = Seq.the_result ("RKstep_round_k4_input_tuple" ^ Int.toString n ^ "unfolding proof failed") (method [] (ctxt, goal))
          val thm = Goal.finish ctxt goal
          val name = Binding.name ("RKstep_round_k4_input_tuple" ^ Int.toString n ^ "_unfold")
          val binding : Attrib.binding = (name, @{attributes [code_unfold]})
          val (_, ctxt) = Local_Theory.note (binding, [thm]) ctxt
      in ctxt
      end\<close>

ML \<open>fun prove_RKstep_round_output_tuple_unfolding n ctxt =
      let val tuple_type = HOLogic.mk_tupleT (map (fn _ => HOLogic.realT) (Library.upto (1,n)))
          val typ =  tuple_type --> HOLogic.realT --> tuple_type --> tuple_type --> tuple_type --> tuple_type --> tuple_type
          val RKstep_round_output = Const (@{const_name RKstep_round_output}, typ)
          val RKstep_round_output_tuple = Proof_Context.read_const {proper=true, strict=true} ctxt ("RKstep_round_output_tuple" ^ Int.toString n)
          val term = @{term Trueprop} $ (Const (@{const_name HOL.eq}, typ --> typ --> HOLogic.boolT) $ RKstep_round_output $ RKstep_round_output_tuple)
          val goal = Goal.init (Thm.cterm_of ctxt term)
          val method = read_method ctxt "(intro ext, auto simp add: RKstep_round_output_prod RKstep_round_output_real_eq)"
          val (ctxt, goal) = Seq.the_result ("RKstep_round_output_tuple" ^ Int.toString n ^ "unfolding proof failed") (method [] (ctxt, goal))
          val thm = Goal.finish ctxt goal
          val name = Binding.name ("RKstep_round_output_tuple" ^ Int.toString n ^ "_unfold")
          val binding : Attrib.binding = (name, @{attributes [code_unfold]})
          val (_, ctxt) = Local_Theory.note (binding, [thm]) ctxt
      in ctxt
      end\<close>

ML \<open>fun prove_RKstep_round_output_tuple_unfolding n ctxt =
      let val tuple_type = HOLogic.mk_tupleT (map (fn _ => HOLogic.realT) (Library.upto (1,n)))
          val typ =  tuple_type --> HOLogic.realT --> tuple_type --> tuple_type --> tuple_type --> tuple_type --> tuple_type
          val RKstep_round_output = Const (@{const_name RKstep_round_output}, typ)
          val RKstep_round_output_tuple = Proof_Context.read_const {proper=true, strict=true} ctxt ("RKstep_round_output_tuple" ^ Int.toString n)
          val term = @{term Trueprop} $ (Const (@{const_name HOL.eq}, typ --> typ --> HOLogic.boolT) $ RKstep_round_output $ RKstep_round_output_tuple)
          val goal = Goal.init (Thm.cterm_of ctxt term)
          val method = read_method ctxt "(intro ext, auto simp add: RKstep_round_output_prod RKstep_round_output_real_eq)"
          val (ctxt, goal) = Seq.the_result ("RKstep_round_output_tuple" ^ Int.toString n ^ "unfolding proof failed") (method [] (ctxt, goal))
          val thm = Goal.finish ctxt goal
          val name = Binding.name ("RKstep_round_output_tuple" ^ Int.toString n ^ "_unfold")
          val binding : Attrib.binding = (name, @{attributes [code_unfold]})
          val (_, ctxt) = Local_Theory.note (binding, [thm]) ctxt
      in ctxt
      end\<close>

ML \<open>fun prove_round_vec_tuple_unfolding n ctxt =
      let val tuple_type = HOLogic.mk_tupleT (map (fn _ => HOLogic.realT) (Library.upto (1,n)))
          val typ =  tuple_type --> tuple_type
          val round_vec = Const (@{const_name round_vec}, typ)
          val round_vec_tuple = Proof_Context.read_const {proper=true, strict=true} ctxt ("round_vec_tuple" ^ Int.toString n)
          val term = @{term Trueprop} $ (Const (@{const_name HOL.eq}, typ --> typ --> HOLogic.boolT) $ round_vec $ round_vec_tuple)
          val goal = Goal.init (Thm.cterm_of ctxt term)
          val method = read_method ctxt "(auto simp add: round_vec_prod round_vec_real)"
          val (ctxt, goal) = Seq.the_result ("round_vec_tuple" ^ Int.toString n ^ "unfolding proof failed") (method [] (ctxt, goal))
          val thm = Goal.finish ctxt goal
          val name = Binding.name ("round_vec_tuple" ^ Int.toString n ^ "_unfold")
          val binding : Attrib.binding = (name, @{attributes [code_unfold]})
          val (_, ctxt) = Local_Theory.note (binding, [thm]) ctxt
      in ctxt
      end\<close>

ML \<open>fun prove_RKstep_round_tuple_unfolding n ctxt =
      let val tuple_type = HOLogic.mk_tupleT (map (fn _ => HOLogic.realT) (Library.upto (1,n)))
          val typ =  (tuple_type --> tuple_type) --> HOLogic.realT --> tuple_type --> tuple_type
          val RKstep_round = Const (@{const_name RKstep_round}, typ)
          val RKstep_round_tuple = Proof_Context.read_const {proper=true, strict=true} ctxt ("RKstep_round_tuple" ^ Int.toString n)
          val term = @{term Trueprop} $ (Const (@{const_name HOL.eq}, typ --> typ --> HOLogic.boolT) $ RKstep_round $ RKstep_round_tuple)
          val goal = Goal.init (Thm.cterm_of ctxt term)
          val n_str = Int.toString n
          val simps = 
            "RKstep_round_def2 RKstep_round_tuple"^n_str^"_def RKstep_round_k2_k3_input_tuple"^n_str^"_unfold"
            ^" RKstep_round_k4_input_tuple"^n_str^"_unfold RKstep_round_output_tuple"^n_str^"_unfold"
            ^" round_vec_tuple"^n_str^"_unfold"
          val method = read_method ctxt ("(intro ext, simp add:"^simps^")")
          val (ctxt, goal) = Seq.the_result ("RKstep_round_tuple" ^ Int.toString n ^ "unfolding proof failed") (method [] (ctxt, goal))
          val thm = Goal.finish ctxt goal
          val name = Binding.name ("RKstep_round_tuple" ^ Int.toString n ^ "_unfold")
          val binding : Attrib.binding = (name, @{attributes [code_unfold]})
          val (_, ctxt) = Local_Theory.note (binding, [thm]) ctxt
      in ctxt
      end\<close>

ML \<open>fun prove_RKstep_round_tuple_lemmas n ctxt =
      ctxt
        |> prove_RKstep_round_k2_k3_input_tuple_unfolding n
        |> prove_RKstep_round_k4_input_tuple_unfolding n
        |> prove_RKstep_round_output_tuple_unfolding n
        |> prove_round_vec_tuple_unfolding n
        |> prove_RKstep_round_tuple_unfolding n
  \<close>

subsubsection \<open>Monomorphisation for arbitrary tuple structures\<close>

ML \<open>Term.exists_subterm\<close>
term RKstep_round
ML \<open>dest_funT\<close>
ML \<open>Thm.full_prop_of @{thm nat.induct} |> Thm.cterm_of @{context}\<close>

ML \<open>fun make_RKstep_round_tuple_monomorphisation n thy =
    Named_Target.theory_map (make_RKstep_round_tuple_defns n) thy |> Named_Target.theory_map (prove_RKstep_round_tuple_lemmas n)\<close>
ML \<open>fun make_RKstep_round_tuple_monomorphisations_upto n = fold make_RKstep_round_tuple_monomorphisation (Library.upto (2,n))\<close>

ML \<open>fun find_RKstep_round_tuple_types (Const (@{const_name RKstep_round}, typ)) =
          let val (fT, _) = dest_funT typ
              val (inpT, _) = dest_funT fT
          in [inpT]
          end
      | find_RKstep_round_tuple_types (Const _) = []
      | find_RKstep_round_tuple_types (t1 $ t2) = find_RKstep_round_tuple_types t1 @ find_RKstep_round_tuple_types t2
      | find_RKstep_round_tuple_types (Abs (_, _, t)) = find_RKstep_round_tuple_types t
      | find_RKstep_round_tuple_types _ = []\<close>

ML \<open>fun make_real_tuple_term (f : string -> term) typ = 
          let fun make_real_tuple_term' str typ =
            case typ of 
              Type (@{type_name prod}, _) => 
                let val typs = HOLogic.strip_tupleT typ
                    val terms = Library.map_index (fn (i, typ) => make_real_tuple_term' (str^"_"^Int.toString i) typ) typs
                in HOLogic.mk_tuple terms
                end
            | Type (@{type_name real}, _) => f str
            | _ => raise TYPE ("RKstep_round instantiation must be for a product of reals", [typ], [])
          in make_real_tuple_term' "" typ
          end\<close>

ML \<open>fun real_tuple_type_to_string typ = 
         case typ of 
            Type (@{type_name prod}, _) => 
              let val typs = HOLogic.strip_tupleT typ
                  val strs = map real_tuple_type_to_string typs
              in "_" ^ String.concat strs ^ "p"
              end
          | Type (@{type_name real}, _) => "R"
          | _ => raise TYPE ("RKstep_round instantiation must be for a product of reals", [typ], [])
         \<close>

ML \<open>fun add_fun_quiet decls specs config lthy =
  let fun pat_completeness_auto ctxt =
        Pat_Completeness.pat_completeness_tac ctxt 1 THEN auto_tac ctxt
      fun prove_termination lthy =
        Function.prove_termination NONE (Function_Common.termination_prover_tac true lthy) lthy
      val (info, lthy) = Function.add_function decls specs config pat_completeness_auto lthy |> snd |> prove_termination
      val morph = Local_Theory.target_morphism lthy
      val terms = map (Morphism.term morph) (#fs info)
  in (terms, lthy)
  end\<close>

ML \<open>fun RKstep_round_k2_k3_input_tuple_defn_term_for_type typ = 
      let val h = Free ("h", HOLogic.realT)
          fun y str = Free ("y" ^ str, HOLogic.realT)
          fun k1k2 str = Free ("k1k2" ^ str, HOLogic.realT)
          fun RKstep_round_k2_k3_input_real str = @{term RKstep_round_k2_k3_input_real} $ h $ y str $ k1k2 str
          val rhs = make_real_tuple_term RKstep_round_k2_k3_input_real typ
          val y_tuple = make_real_tuple_term y typ
          val k1k2_tuple = make_real_tuple_term k1k2 typ
          val RKstep_round_k2_k3_input_tuple_term =
            Free ("RKstep_round_k2_k3_input" ^ real_tuple_type_to_string typ, HOLogic.realT --> typ --> typ --> typ)
          val lhs = RKstep_round_k2_k3_input_tuple_term $ h $ y_tuple $ k1k2_tuple
      in @{term Trueprop} $ (Const (@{const_name HOL.eq}, typ --> typ --> HOLogic.boolT) $ lhs $ rhs)
      end\<close>
ML \<open>fun make_RKstep_round_k2_k3_input_tuple_defn_for_type typ ctxt =
      let val decl_type = HOLogic.realT --> typ --> typ --> typ
          val decl = (Binding.make ("RKstep_round_k2_k3_input" ^ real_tuple_type_to_string typ, @{here}), SOME decl_type, NoSyn)
          val spec = ((Binding.empty_atts, RKstep_round_k2_k3_input_tuple_defn_term_for_type typ), [], [])
      in add_fun_quiet [decl] [spec] Function_Fun.fun_config ctxt |> apfst hd
      end\<close>

ML \<open>fun RKstep_round_k4_input_tuple_defn_term_for_type typ = 
      let val h = Free ("h", HOLogic.realT)
          fun y str = Free ("y" ^ str, HOLogic.realT)
          fun k3 str = Free ("k3" ^ str, HOLogic.realT)
          fun RKstep_round_k4_input_real str= @{term RKstep_round_k4_input_real} $ h $ y str $ k3 str
          val rhs = make_real_tuple_term RKstep_round_k4_input_real typ
          val y_tuple = make_real_tuple_term y typ
          val k3_tuple = make_real_tuple_term k3 typ
          val RKstep_round_k4_input_tuple_term =
            Free ("RKstep_round_k4_input" ^ real_tuple_type_to_string typ, HOLogic.realT --> typ --> typ --> typ)
          val lhs = RKstep_round_k4_input_tuple_term $ h $ y_tuple $ k3_tuple
      in @{term Trueprop} $ (Const (@{const_name HOL.eq}, typ --> typ --> HOLogic.boolT) $ lhs $ rhs)
      end\<close>
ML \<open>fun make_RKstep_round_k4_input_tuple_defn_for_type typ ctxt =
      let val decl_type = HOLogic.realT --> typ --> typ --> typ
          val decl = (Binding.make ("RKstep_round_k4_input" ^ real_tuple_type_to_string typ, @{here}), SOME decl_type, NoSyn)
          val spec = ((Binding.empty_atts, RKstep_round_k4_input_tuple_defn_term_for_type typ), [], [])
      in add_fun_quiet [decl] [spec] Function_Fun.fun_config ctxt |> apfst hd
      end\<close>

ML \<open>fun RKstep_round_output_tuple_defn_term_for_type typ = 
      let val h = Free ("h", HOLogic.realT)
          fun y str = Free ("y" ^ str, HOLogic.realT)
          fun k1 str = Free ("k1" ^ str, HOLogic.realT)
          fun k2 str = Free ("k2" ^ str, HOLogic.realT)
          fun k3 str = Free ("k3" ^ str, HOLogic.realT)
          fun k4 str = Free ("k4" ^ str, HOLogic.realT)
          fun RKstep_round_output_real str = @{term RKstep_round_output_real} $ y str $ h $ k1 str $ k2 str $ k3 str $ k4 str
          val rhs = make_real_tuple_term RKstep_round_output_real typ
          val y_tuple = make_real_tuple_term y typ
          val k1_tuple = make_real_tuple_term k1 typ
          val k2_tuple = make_real_tuple_term k2 typ
          val k3_tuple = make_real_tuple_term k3 typ
          val k4_tuple = make_real_tuple_term k4 typ
          val fun_typ = typ --> HOLogic.realT --> typ --> typ --> typ --> typ --> typ
          val RKstep_round_output_tuple_term = Free ("RKstep_round_output" ^ real_tuple_type_to_string typ, fun_typ)
          val lhs = RKstep_round_output_tuple_term $ y_tuple $ (Free ("h", HOLogic.realT)) $ k1_tuple $ k2_tuple $ k3_tuple $ k4_tuple
      in @{term Trueprop} $ (Const (@{const_name HOL.eq}, typ --> typ --> HOLogic.boolT) $ lhs $ rhs)
      end\<close>
ML \<open>fun make_RKstep_round_output_tuple_defn_for_type typ ctxt =
      let val decl_type = typ --> HOLogic.realT --> typ --> typ --> typ --> typ --> typ
          val decl = (Binding.make ("RKstep_round_output" ^ real_tuple_type_to_string typ, @{here}), SOME decl_type, NoSyn)
          val spec = ((Binding.empty_atts, RKstep_round_output_tuple_defn_term_for_type typ), [], [])
      in add_fun_quiet [decl] [spec] Function_Fun.fun_config ctxt |> apfst hd
      end\<close>

ML \<open>fun make_round_vec_tuple_defn_for_type typ ctxt =
      let val decl_type = typ --> typ
          val decl = (Binding.make ("round_vec" ^ real_tuple_type_to_string typ, @{here}), SOME decl_type, NoSyn)
          fun x str = Free ("x" ^ str, HOLogic.realT)
          val rhs = make_real_tuple_term (fn str => @{term round_Scaled} $ x str) typ
          val x_tuple = make_real_tuple_term x typ
          val lhs = Free ("round_vec" ^ real_tuple_type_to_string typ, typ --> typ) $ x_tuple
          val term = @{term Trueprop} $ (Const (@{const_name HOL.eq}, typ --> typ --> HOLogic.boolT) $ lhs $ rhs)
          val spec = ((Binding.empty_atts, term), [], [])
      in add_fun_quiet [decl] [spec] Function_Fun.fun_config ctxt |> apfst hd
      end\<close>

ML \<open>fun make_RKstep_round_tuple_defn_for_type typ (RKstep_round_k2_k3_input, RKstep_round_k4_input, RKstep_round_output, round_vec) ctxt =
      let val output_term = RKstep_round_output $ Bound 5 $ Bound 6 $ Bound 3 $ Bound 2 $ Bound 1 $ Bound 0
          val k4_abs_term = Abs ("k4", typ, output_term)
          val k4_term = (Bound 3 $ (RKstep_round_k4_input $ Bound 5 $ Bound 4 $ Bound 0))
          val k4_let_term = Const ("HOL.Let", typ --> (typ --> typ) --> typ) $ k4_term $ k4_abs_term
          val k3_abs_term = Abs ("k3", typ, k4_let_term)
          val k3_term = (Bound 2 $ (RKstep_round_k2_k3_input $ Bound 4 $ Bound 3 $ Bound 0))
          val k3_let_term = Const ("HOL.Let", typ --> (typ --> typ) --> typ) $ k3_term $ k3_abs_term
          val k2_abs_term = Abs ("k2", typ, k3_let_term)
          val k2_term = (Bound 1 $ (RKstep_round_k2_k3_input $ Bound 3 $ Bound 2 $ Bound 0))
          val k2_let_term = Const ("HOL.Let", typ --> (typ --> typ) --> typ) $ k2_term $ k2_abs_term
          val k1_abs_term = Abs ("k1", typ, k2_let_term)
          val k1_term = (Bound 0 $ Bound 1)
          val k1_let_term = Const ("HOL.Let", typ --> (typ --> typ) --> typ) $ k1_term $ k1_abs_term
          val f'_abs_term = Abs ("f'", typ --> typ, k1_let_term)
          val f'_term = (Const ("Fun.comp", (typ --> typ) --> (typ --> typ) --> typ --> typ) $ round_vec $ Free ("f", typ --> typ))
          val f'_let_term = Const ("HOL.Let", (typ --> typ) --> ((typ --> typ) --> typ) --> typ) $ f'_term $ f'_abs_term
          val y'_abs_term = Abs ("y'", typ, f'_let_term)
          val y'_term = (round_vec $ Free ("y", typ))
          val y'_let_term = Const ("HOL.Let", typ --> (typ --> typ) --> typ) $ y'_term $ y'_abs_term
          val h'_abs_term = Abs ("h'", HOLogic.realT, y'_let_term)
          val h'_term = (@{term round_Scaled} $ Free ("h", HOLogic.realT))
          val h'_let_term = Const ("HOL.Let", HOLogic.realT --> (HOLogic.realT --> typ) --> typ) $ h'_term $ h'_abs_term
          val rhs = h'_let_term
          val fun_typ = (typ --> typ) --> HOLogic.realT --> typ --> typ
          val RKstep_round_tuple_term = Free ("RKstep_round_tuple" ^ real_tuple_type_to_string typ, fun_typ)
          val lhs = RKstep_round_tuple_term $ (Free ("f", typ --> typ)) $ (Free ("h", HOLogic.realT)) $ (Free ("y", typ))
          val term = @{term Trueprop} $ (Const (@{const_name HOL.eq}, typ --> typ --> HOLogic.boolT) $ lhs $ rhs)
          val decl = (Binding.make ("RKstep_round_tuple" ^ real_tuple_type_to_string typ, @{here}), NONE, NoSyn)
          val spec = (Binding.empty_atts, term)
          fun lift (t, lthy) = (Morphism.term (Local_Theory.target_morphism lthy) t, lthy)
      in Specification.definition (SOME decl) [] [] spec ctxt |> apfst fst |> lift
      end\<close>

ML \<open>fun make_RKstep_round_tuple_defns_for_type typ ctxt =
      let val (RKstep_round_k2_k3_input, ctxt) = make_RKstep_round_k2_k3_input_tuple_defn_for_type typ ctxt
          val (RKstep_round_k4_input, ctxt) = make_RKstep_round_k4_input_tuple_defn_for_type typ ctxt
          val (RKstep_round_output, ctxt) = make_RKstep_round_output_tuple_defn_for_type typ ctxt
          val (round_vec, ctxt) = make_round_vec_tuple_defn_for_type typ ctxt
          val consts = (RKstep_round_k2_k3_input, RKstep_round_k4_input, RKstep_round_output, round_vec)
          val (RKstep_round, ctxt) =  make_RKstep_round_tuple_defn_for_type typ consts ctxt    
          val consts = (RKstep_round_k2_k3_input, RKstep_round_k4_input, RKstep_round_output, round_vec, RKstep_round)
      in (consts, ctxt)
      end\<close>

ML \<open>fun prove_RKstep_round_k2_k3_input_tuple_unfolding_for_type RKstep_round_k2_k3_input_tuple ctxt =
      let val (name, typ) =
            case RKstep_round_k2_k3_input_tuple of
                Const x => x
              | _ => raise TERM ("RKstep_round_k2_k3_input_tuple term must be a constant", [RKstep_round_k2_k3_input_tuple])
          val RKstep_round_k2_k3_input = Const (@{const_name RKstep_round_k2_k3_input}, typ)
          val term = @{term Trueprop} $ (Const (@{const_name HOL.eq}, typ --> typ --> HOLogic.boolT) $ RKstep_round_k2_k3_input $ RKstep_round_k2_k3_input_tuple)
          val goal = Goal.init (Thm.cterm_of ctxt term)
          val method = read_method ctxt "(intro ext, auto simp add: RKstep_round_k2_k3_input_prod RKstep_round_k2_k3_input_real_eq)"
          val (ctxt, goal) = Seq.the_result (name ^ "unfolding proof failed") (method [] (ctxt, goal))
          val thm = Goal.finish ctxt goal
          val base_name = Long_Name.base_name name
          val name = Binding.name (base_name ^ "_unfold")
          val binding : Attrib.binding = (name, @{attributes [code_unfold]})
          val ((thm_name, _), ctxt) = Local_Theory.note (binding, [thm]) ctxt
      in (thm_name, ctxt)
      end\<close>

ML \<open>fun prove_RKstep_round_k4_input_tuple_unfolding_for_type RKstep_round_k4_input_tuple ctxt =
      let val (name, typ) =
            case RKstep_round_k4_input_tuple of
                Const x => x
              | _ => raise TERM ("RKstep_round_k4_input_tuple term must be a constant", [RKstep_round_k4_input_tuple])
          val RKstep_round_k4_input = Const (@{const_name RKstep_round_k4_input}, typ)
          val term = @{term Trueprop} $ (Const (@{const_name HOL.eq}, typ --> typ --> HOLogic.boolT) $ RKstep_round_k4_input $ RKstep_round_k4_input_tuple)
          val goal = Goal.init (Thm.cterm_of ctxt term)
          val method = read_method ctxt "(intro ext, auto simp add: RKstep_round_k4_input_prod RKstep_round_k4_input_real_eq)"
          val (ctxt, goal) = Seq.the_result (name ^ "unfolding proof failed") (method [] (ctxt, goal))
          val thm = Goal.finish ctxt goal
          val base_name = Long_Name.base_name name
          val name = Binding.name (base_name ^ "_unfold")
          val binding : Attrib.binding = (name, @{attributes [code_unfold]})
          val ((thm_name, _), ctxt) = Local_Theory.note (binding, [thm]) ctxt
      in (thm_name, ctxt)
      end\<close>

ML \<open>fun prove_RKstep_round_output_tuple_unfolding_for_type RKstep_round_output_tuple ctxt =
      let val (name, typ) =
            case RKstep_round_output_tuple of
                Const x => x
              | _ => raise TERM ("RKstep_round_output_tuple term must be a constant", [RKstep_round_output_tuple])
          val RKstep_round_output = Const (@{const_name RKstep_round_output}, typ)
          val term = @{term Trueprop} $ (Const (@{const_name HOL.eq}, typ --> typ --> HOLogic.boolT) $ RKstep_round_output $ RKstep_round_output_tuple)
          val goal = Goal.init (Thm.cterm_of ctxt term)
          val method = read_method ctxt "(intro ext, auto simp add: RKstep_round_output_prod RKstep_round_output_real_eq)"
          val (ctxt, goal) = Seq.the_result (name ^ "unfolding proof failed") (method [] (ctxt, goal))
          val thm = Goal.finish ctxt goal
          val base_name = Long_Name.base_name name
          val name = Binding.name (base_name ^ "_unfold")
          val binding : Attrib.binding = (name, @{attributes [code_unfold]})
          val ((thm_name, _), ctxt) = Local_Theory.note (binding, [thm]) ctxt
      in (thm_name, ctxt)
      end\<close>


ML \<open>fun prove_round_vec_tuple_unfolding_for_type round_vec_tuple ctxt =
      let val (name, typ) =
            case round_vec_tuple of
                Const x => x
              | _ => raise TERM ("round_vec_tuple term must be a constant", [round_vec_tuple])
          val round_vec = Const (@{const_name round_vec}, typ)
          val term = @{term Trueprop} $ (Const (@{const_name HOL.eq}, typ --> typ --> HOLogic.boolT) $ round_vec $ round_vec_tuple)
          val goal = Goal.init (Thm.cterm_of ctxt term)
          val method = read_method ctxt "(auto simp add: round_vec_prod round_vec_real)"
          val (ctxt, goal) = Seq.the_result (name ^ "unfolding proof failed") (method [] (ctxt, goal))
          val thm = Goal.finish ctxt goal
          val base_name = Long_Name.base_name name
          val name = Binding.name (base_name ^ "_unfold")
          val binding : Attrib.binding = (name, @{attributes [code_unfold]})
          val ((thm_name, _), ctxt) = Local_Theory.note (binding, [thm]) ctxt
      in (thm_name, ctxt)
      end\<close>

ML \<open>fun prove_RKstep_round_tuple_unfolding_for_type RKstep_round_tuple unfolds ctxt =
      let val (name, typ) =
            case RKstep_round_tuple of
                Const x => x
              | _ => raise TERM ("RKstep_round_tuple term must be a constant", [RKstep_round_tuple])
          val RKstep_round = Const (@{const_name RKstep_round}, typ)
          val term = @{term Trueprop} $ (Const (@{const_name HOL.eq}, typ --> typ --> HOLogic.boolT) $ RKstep_round $ RKstep_round_tuple)
          val goal = Goal.init (Thm.cterm_of ctxt term)
          val simps = 
            "RKstep_round_def2 "^name^"_def " ^ Library.implode_space unfolds
          val method = read_method ctxt ("(intro ext, simp add:"^simps^")")
          val (ctxt, goal) = Seq.the_result (name ^ "unfolding proof failed") (method [] (ctxt, goal))
          val thm = Goal.finish ctxt goal
          val base_name = Long_Name.base_name name
          val name = Binding.name (base_name ^ "_unfold")
          val binding : Attrib.binding = (name, @{attributes [code_unfold]})
      in Local_Theory.note (binding, [thm]) ctxt
      end\<close>

ML \<open>fun prove_RKstep_round_tuple_lemmas_for_type (RKstep_round_k2_k3_input, RKstep_round_k4_input, RKstep_round_output, round_vec, RKstep_round) ctxt =
          let val (RKstep_round_k2_k3_input_unfold, ctxt) = prove_RKstep_round_k2_k3_input_tuple_unfolding_for_type RKstep_round_k2_k3_input ctxt
              val (RKstep_round_k4_input_unfold, ctxt) = prove_RKstep_round_k4_input_tuple_unfolding_for_type RKstep_round_k4_input ctxt
              val (RKstep_round_output_unfold, ctxt) = prove_RKstep_round_output_tuple_unfolding_for_type RKstep_round_output ctxt
              val (round_vec_unfold, ctxt) = prove_round_vec_tuple_unfolding_for_type round_vec ctxt
              val unfolds = [RKstep_round_k2_k3_input_unfold, RKstep_round_k4_input_unfold, RKstep_round_output_unfold, round_vec_unfold]
          in prove_RKstep_round_tuple_unfolding_for_type RKstep_round unfolds ctxt |> snd
          end\<close>

ML \<open>fun make_RKstep_round_tuple_monomorphisation_for_type typ ctxt =
      let val (_, ctxt) = Local_Theory.begin_nested ctxt
          val (decls, ctxt) = make_RKstep_round_tuple_defns_for_type typ ctxt
          val ctxt = Local_Theory.end_nested ctxt
          val (_, ctxt) = Local_Theory.begin_nested ctxt
          val ctxt =  prove_RKstep_round_tuple_lemmas_for_type decls ctxt
      in Local_Theory.end_nested ctxt
      end\<close>

named_theorems cyphyaction_defs

ML \<open>fun unfold_cyphyaction_defs ctxt t =
          let val rec_sys_defs = Named_Theorems.get ctxt @{named_theorems "rec_sys_defs"}
              val recursive_defs = Named_Theorems.get ctxt @{named_theorems "recursive_defs"}
              val cyphyaction_defs = Named_Theorems.get ctxt @{named_theorems "cyphyaction_defs"}
              val defs = cyphyaction_defs @ rec_sys_defs @ recursive_defs
              val simps = Library.maps (Simplifier.mksimps ctxt) defs
              val thy = Proof_Context.theory_of ctxt
          in Raw_Simplifier.rewrite_term thy simps [] t
          end\<close>

ML \<open>fun lens_view_type (Type (@{type_name "lens_ext"}, [view, _, _])) = view
      | lens_view_type T = raise TYPE ("lens_view_type", [T], [])\<close>

ML List.foldr
ML \<open>fun collect_CEvolve_types (Const (@{const_name cEvolve},_) $ t) = [lens_view_type (Term.fastype_of t)]
      | collect_CEvolve_types (t1 $ t2) =  collect_CEvolve_types t1 @ collect_CEvolve_types t2
      | collect_CEvolve_types (Abs (_, _, t)) = collect_CEvolve_types t
      | collect_CEvolve_types _ = []\<close>

ML \<open>fun ensure_monomorphisations_exist ctxt term =
          let val unfolded_term = unfold_cyphyaction_defs ctxt term
              val typs = collect_CEvolve_types unfolded_term
              fun unfold_name typ = "RKstep_round_tuple" ^ real_tuple_type_to_string typ
              fun has_unfold typ ctxt = can (Proof_Context.read_const {proper=true, strict=true} ctxt) (unfold_name typ)
              fun lift_cond f g a b = (f a b ? g a) b
              val check_and_make = lift_cond (not oo has_unfold) make_RKstep_round_tuple_monomorphisation_for_type
          in fold check_and_make typs ctxt
          end\<close>

subsection \<open>Support for lifting recursion into the code datatype\<close>

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

instantiation "fun" ::  (type,recursive_system) recursive_system 
begin
definition [code_unfold]: "bottom_fun \<equiv> \<lambda>x. bottom"
definition total_actions_fun :: "('a \<Rightarrow> 'b) itself \<Rightarrow> \<nat>" where
  [code_unfold]: "total_actions_fun _ \<equiv> (total_actions TYPE('b))"
instance ..
end

lemma funpow_code [code]:
  "Nat.funpow n f x = (if n = 0 then x else Nat.funpow (n - 1) f (f x))"
  by (induct n, auto simp add: Nat.funpow_code_def gr0_conv_Suc)

subsection \<open>Code datatype definition\<close>

axiomatization
  cEvolve' :: "(real \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('e, 's) cyphyaction" and
  cInputPrefix' :: "('e \<Rightarrow> (('s \<Rightarrow> \<bool>) \<times> ('e, 's) cyphyaction) option) \<Rightarrow> 'e \<Rightarrow> ('e, 's) cyphyaction" and
  cOutputPrefix' :: "('s \<Rightarrow> 'e) \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction" and
  cParallelAct' :: "('s \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> 'e set \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction" and
  cRec' :: "nat \<Rightarrow> (nat \<Rightarrow> ('e, 's) cyphyaction) \<Rightarrow> ('e, 's) cyphyaction" and
  cRename' :: "('e \<leftrightarrow> 'e) \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction"
where
  cEvolve_cEvolve'[code_unfold]:
    "cEvolve v f p \<equiv> cEvolve' (\<lambda>r s. put\<^bsub>v\<^esub> s (RKstep_round (\<lambda>x. get\<^bsub>v\<^esub> (f (put\<^bsub>v\<^esub> s x))) r (get\<^bsub>v\<^esub> s))) p" and
  cInputPrefix_cInputPrefix'[code_unfold]:
    "cInputPrefix c S F \<equiv> cInputPrefix' (\<lambda>e.  map_option F ((match\<^bsub>c\<^esub> e) \<bind> (map_id_on S))) (build\<^bsub>c\<^esub> default)" and
  cOutputPrefix_cOutputPrefix'[code_unfold]:
    "cOutputPrefix c expr P \<equiv> cOutputPrefix' (build\<^bsub>c\<^esub> \<circ> expr) P" and
  cParallelAct_cParallelAct'[code_unfold]:
    "cParallelAct ns1 ns2 cs P Q \<equiv> cParallelAct' (\<lambda> s0 s1 s2. s0 \<triangleleft>\<^bsub>ns1\<^esub> s1 \<triangleleft>\<^bsub>ns2\<^esub> s2) cs P Q" and
  nu_cRec'1[code_unfold]:
    "\<nu> FF \<equiv> cRec' (total_actions TYPE(('e, 's) cyphyaction)) (\<lambda>n. Nat.funpow n FF bottom)" and
  nu_cRec'2[code_unfold]:
    "g (\<nu> FF') \<equiv> cRec' (total_actions TYPE('p)) (\<lambda>n. g (Nat.funpow n FF' bottom))" and
  nu_cRec'3[code_unfold]:
    "(\<nu> FF'') \<equiv> \<lambda>x. cRec' (total_actions TYPE(('x \<Rightarrow> ('e, 's) cyphyaction))) (\<lambda>n. Nat.funpow n FF'' bottom x)" and
  nu_cRec'4[code_unfold]:
    "g' (\<nu> FF') \<equiv> \<lambda>x. cRec' (total_actions TYPE('p)) (\<lambda>n. g' (Nat.funpow n FF' bottom) x)" and
  cRename_cRename'[code_unfold]:
    "cRename rel P = cRename' rel P"
  for v :: "'b :: round_vector \<Longrightarrow> 's"
and FF :: "('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction"
and FF' :: "'p::recursive_system \<Rightarrow> 'p::recursive_system"
and FF'' :: "('x \<Rightarrow> ('e, 's) cyphyaction) \<Rightarrow> ('x \<Rightarrow> ('e, 's) cyphyaction)"
and g :: "'p \<Rightarrow> ('e, 's) cyphyaction"
and g' :: "'p \<Rightarrow> 'x \<Rightarrow> ('e, 's) cyphyaction"
and f :: "'s \<Rightarrow> 's"
and p :: "'s \<Rightarrow> bool"

named_theorems cyphyaction_datatype_unfolds 
lemmas [cyphyaction_datatype_unfolds] = cEvolve_cEvolve' cInputPrefix_cInputPrefix' cOutputPrefix_cOutputPrefix' cParallelAct_cParallelAct' nu_cRec'1 nu_cRec'2

code_datatype cSkip cAssigns cStop cChaos cAssume cEvolve' cSyncPrefix cEventPrefix cOutputPrefix' cInputPrefix'
  cSeq cGuard cCond "inf :: ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction"
  cExtChoice cParallelAct' cRec' cHide cRename' cInterruptCond cTimeout

section \<open>AST datatype for manipulation in Isabelle\<close>

datatype ('e, 's) cyphyast =
  astSkip | astAssigns "'s \<Rightarrow> 's" | astStop | astChaos | astAssume "'s \<Rightarrow> bool" | astEvolve "real \<Rightarrow> 's \<Rightarrow> 's" "'s \<Rightarrow> bool"
| astSyncPrefix "(unit, 'e) channel" "('e, 's) cyphyast" | astEventPrefix 'e "('e, 's) cyphyast"
| astOutputPrefix "'s \<Rightarrow> 'e" "('e, 's) cyphyast" | astInputPrefix "('e \<Rightarrow> (('s \<Rightarrow> \<bool>) \<times> ('e, 's) cyphyast) option)" 'e
| astSeq "('e, 's) cyphyast" "('e, 's) cyphyast" | astGuard "'s \<Rightarrow> bool" "('e, 's) cyphyast" | astCond "'s \<Rightarrow> bool" "('e, 's) cyphyast" "('e, 's) cyphyast"
| astIntChoice "('e, 's) cyphyast" "('e, 's) cyphyast" | astExtChoice "('e, 's) cyphyast" "('e, 's) cyphyast"
| astParallelAct "'s \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's" "'e set" "('e, 's) cyphyast" "('e, 's) cyphyast"
| astRec nat "nat \<Rightarrow> ('e, 's) cyphyast" | astHide "('e, 's) cyphyast" "'e set" | astRename "'e \<leftrightarrow> 'e" "('e, 's) cyphyast"
| astInterruptCond "('e, 's) cyphyast" "'s \<Rightarrow> bool" | astTimeout "('e, 's) cyphyast" "'s \<Rightarrow> real" "('e, 's) cyphyast"
print_theorems
primrec cyphyast_to_cyphyaction :: "('e, 's) cyphyast \<Rightarrow> ('e, 's) cyphyaction" where
  "cyphyast_to_cyphyaction astSkip = cSkip"
| "cyphyast_to_cyphyaction (astAssigns subst) = cAssigns subst"
| "cyphyast_to_cyphyaction astStop = cStop"
| "cyphyast_to_cyphyaction astChaos = cChaos"
| "cyphyast_to_cyphyaction (astAssume pred) = cAssume pred"
| "cyphyast_to_cyphyaction (astEvolve f pred) = cEvolve' f pred"
| "cyphyast_to_cyphyaction (astSyncPrefix e P) = cSyncPrefix e (cyphyast_to_cyphyaction P)"
| "cyphyast_to_cyphyaction (astEventPrefix e P) = cEventPrefix e (cyphyast_to_cyphyaction P)"
| "cyphyast_to_cyphyaction (astOutputPrefix f P) = cOutputPrefix' f (cyphyast_to_cyphyaction P)"
| "cyphyast_to_cyphyaction (astInputPrefix F e) = cInputPrefix' (\<lambda>x. map_option (map_prod id cyphyast_to_cyphyaction) (F x)) e"
| "cyphyast_to_cyphyaction (astSeq P Q) = cSeq (cyphyast_to_cyphyaction P) (cyphyast_to_cyphyaction Q)"
| "cyphyast_to_cyphyaction (astGuard pred P) = cGuard pred (cyphyast_to_cyphyaction P)"
| "cyphyast_to_cyphyaction (astCond pred P Q) = cCond (cyphyast_to_cyphyaction P) pred (cyphyast_to_cyphyaction Q)"
| "cyphyast_to_cyphyaction (astIntChoice P Q) = inf (cyphyast_to_cyphyaction P) (cyphyast_to_cyphyaction Q)"
| "cyphyast_to_cyphyaction (astExtChoice P Q) = cExtChoice (cyphyast_to_cyphyaction P) (cyphyast_to_cyphyaction Q)"
| "cyphyast_to_cyphyaction (astParallelAct mrg cs P Q) = cParallelAct' mrg cs (cyphyast_to_cyphyaction P) (cyphyast_to_cyphyaction Q)"
| "cyphyast_to_cyphyaction (astRec n F) = cRec' n (\<lambda>n. cyphyast_to_cyphyaction (F n))"
| "cyphyast_to_cyphyaction (astHide P S) = cHide (cyphyast_to_cyphyaction P) S"
| "cyphyast_to_cyphyaction (astRename renames P) = cRename' renames (cyphyast_to_cyphyaction P)"
| "cyphyast_to_cyphyaction (astInterruptCond P pred) = cInterruptCond (cyphyast_to_cyphyaction P) pred"
| "cyphyast_to_cyphyaction (astTimeout P f Q) = cTimeout (cyphyast_to_cyphyaction P) f (cyphyast_to_cyphyaction Q)"

definition cyphyaction_to_cyphyast :: "('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyast" where
  [code del]: "cyphyaction_to_cyphyast P = (SOME Q. cyphyast_to_cyphyaction Q = P)"
ML apsnd
code_printing 
  constant cyphyaction_to_cyphyast => (SML)
      "(fn ast => 
          let fun cyphyaction'_to'_cyphyast CSkip = AstSkip
                | cyphyaction'_to'_cyphyast (CAssigns subst) = AstAssigns subst
                | cyphyaction'_to'_cyphyast CStop = AstStop
                | cyphyaction'_to'_cyphyast CChaos = AstChaos
                | cyphyaction'_to'_cyphyast (CAssume pred) = AstAssume pred
                | cyphyaction'_to'_cyphyast (CEvolve (f, pred)) = AstEvolve (f, pred)
                | cyphyaction'_to'_cyphyast (CSyncPrefix (e, P)) = AstSyncPrefix (e, cyphyaction'_to'_cyphyast P)
                | cyphyaction'_to'_cyphyast (CEventPrefix (e, P)) = AstEventPrefix (e, cyphyaction'_to'_cyphyast P)
                | cyphyaction'_to'_cyphyast (COutputPrefix (f, P)) = AstOutputPrefix (f, cyphyaction'_to'_cyphyast P)
                | cyphyaction'_to'_cyphyast (CInputPrefix (F, e)) = AstInputPrefix (fn x => Option.map (apsnd cyphyaction'_to'_cyphyast) (F x), e)
                | cyphyaction'_to'_cyphyast (CSeq (P, Q)) = AstSeq (cyphyaction'_to'_cyphyast P, cyphyaction'_to'_cyphyast Q)
                | cyphyaction'_to'_cyphyast (CGuard (pred, P)) = AstGuard (pred, cyphyaction'_to'_cyphyast P)
                | cyphyaction'_to'_cyphyast (CCond (P, pred, Q)) = AstCond (pred, cyphyaction'_to'_cyphyast P, cyphyaction'_to'_cyphyast Q)
                | cyphyaction'_to'_cyphyast (Inf'_cyphyaction (P, Q)) = AstIntChoice (cyphyaction'_to'_cyphyast P, cyphyaction'_to'_cyphyast Q)
                | cyphyaction'_to'_cyphyast (CExtChoice (P, Q)) = AstExtChoice (cyphyaction'_to'_cyphyast P, cyphyaction'_to'_cyphyast Q)
                | cyphyaction'_to'_cyphyast (CParallelAct (mrg, cs, P, Q)) = AstParallelAct (mrg, cs, cyphyaction'_to'_cyphyast P, cyphyaction'_to'_cyphyast Q)
                | cyphyaction'_to'_cyphyast (CRec (n, F)) = AstRec (n, fn n => cyphyaction'_to'_cyphyast (F n))
                | cyphyaction'_to'_cyphyast (CHide (P, S)) = AstHide (cyphyaction'_to'_cyphyast P, S)
                | cyphyaction'_to'_cyphyast (CRename (renames, P)) = AstRename (renames, cyphyaction'_to'_cyphyast P)
                | cyphyaction'_to'_cyphyast (CInterruptCond (P, pred)) = AstInterruptCond (cyphyaction'_to'_cyphyast P, pred)
                | cyphyaction'_to'_cyphyast (CTimeout (P, n, Q)) = AstTimeout (cyphyaction'_to'_cyphyast P, n, cyphyaction'_to'_cyphyast Q)
          in cyphyaction'_to'_cyphyast ast end)"

section \<open>Operational semantics for trace checking\<close>

datatype 'e visibility = Visible 'e | Hidden nat 'e

datatype ('e, 's) cyphystep =
  Termination bool 's
  | Timestep 's bool "('e, 's) cyphyast"
  | StUpd 's bool "('e, 's) cyphyast"
  | EventStep "('e, 's) cyphyast"

fun is_Timestep where "is_Timestep (Timestep s strict P) = True" | "is_Timestep _ = False"
fun is_Termination where "is_Termination (Termination strict s) = True" | "is_Termination _ = False"
fun is_StUpd where "is_StUpd (StUpd strict s P) = True" | "is_StUpd _ = False"
fun is_EventStep where "is_EventStep (EventStep P) = True" | "is_EventStep _ = False"

fun map_cyphystep_continuation :: "(('e, 's) cyphyast \<Rightarrow> ('e, 's) cyphyast) \<Rightarrow> ('e, 's) cyphystep \<Rightarrow> ('e, 's) cyphystep" where
  "map_cyphystep_continuation f (Termination b s) = Termination b s"
| "map_cyphystep_continuation f (Timestep s b P) = Timestep s b (f P)"
| "map_cyphystep_continuation f (StUpd s b P) = StUpd s b (f P)"
| "map_cyphystep_continuation f (EventStep P) = EventStep (f P)"

fun rapply_alist :: "('a \<times> 'b) list \<Rightarrow> 'b \<Rightarrow> 'a list" where
  "rapply_alist [] _ = []"
| "rapply_alist ((x, y) # xs) b = (if fast_equal b y then [x] else []) @ rapply_alist xs b"

fun group_cyphysteps :: "('e, 's) cyphystep list  \<Rightarrow>
    (bool \<times> 's) list
      \<times> ('s \<times> bool \<times> ('e, 's) cyphyast) list
      \<times> ('s \<times> bool \<times> ('e, 's) cyphyast) list
      \<times> ('e, 's) cyphyast list" where
  "group_cyphysteps [] = ([], [], [], [])"
| "group_cyphysteps (Termination b s # steps) = apfst ((#) (b, s)) (group_cyphysteps steps)"
| "group_cyphysteps (Timestep s strict P # steps) = apsnd (apfst ((#) (s, strict, P))) (group_cyphysteps steps)"
| "group_cyphysteps (StUpd s b P # steps) = apsnd (apsnd (apfst ((#) (s, b, P)))) (group_cyphysteps steps)"
| "group_cyphysteps (EventStep P # steps) = apsnd (apsnd (apsnd ((#) P))) (group_cyphysteps steps)"


primrec rec_depth :: "nat \<Rightarrow> ('e, 's) cyphyast \<Rightarrow> nat" where
  "rec_depth n astSkip = 0"
| "rec_depth n (astAssigns _) = 0"
| "rec_depth n astStop = 0"
| "rec_depth n astChaos = 0"
| "rec_depth n (astAssume _) = 0"
| "rec_depth n (astEvolve _ _) = 0"
| "rec_depth n (astSyncPrefix _ P) = rec_depth n P"
| "rec_depth n (astEventPrefix _ P) = rec_depth n P"
| "rec_depth n (astOutputPrefix _ P) = rec_depth n P"
| "rec_depth n (astInputPrefix F _) = 0"
| "rec_depth n (astSeq P Q) = max (rec_depth n P) (rec_depth n Q)"
| "rec_depth n (astIntChoice P Q) = max (rec_depth n P) (rec_depth n Q)"
| "rec_depth n (astExtChoice P Q) = max (rec_depth n P) (rec_depth n Q)"
| "rec_depth n (astGuard _ P) = rec_depth n P"
| "rec_depth n (astCond _ P Q) = max (rec_depth n P) (rec_depth n Q)"
| "rec_depth n (astInterruptCond P _) = rec_depth n P"
| "rec_depth n (astTimeout P _ Q) = max (rec_depth n P) (rec_depth n Q)"
| "rec_depth n (astParallelAct _ _ P Q) = max (rec_depth n P) (rec_depth n Q)"
| "rec_depth n (astHide P _) = rec_depth n P"
| "rec_depth n (astRename _ P) = rec_depth n P"
| "rec_depth n (astRec m FF) = 1 + rec_depth n (FF (n*m))"

fun make_strict_internal :: "('e, 's) cyphystep \<Rightarrow> ('e, 's) cyphystep" where
  "make_strict_internal (Termination _ s) = Termination True s"
| "make_strict_internal (Timestep s b P) = Timestep s b P"
| "make_strict_internal (StUpd s _ P) = StUpd s True P"
| "make_strict_internal (EventStep P) = EventStep P"

function (sequential) step_cyphyaction :: "real \<Rightarrow> nat \<Rightarrow> 'e visibility list \<Rightarrow> 's \<Rightarrow> ('e, 's) cyphyast \<Rightarrow> ('e, 's) cyphystep list option" where
  (* Skip: terminate immediately *)
  "step_cyphyaction timestep n t s astSkip = Some [Termination False s]"
  (* Assigns: terminate immediately with updated state *)
| "step_cyphyaction timestep n t s (astAssigns subst) = Some [Termination False (subst s)]"
  (* Stop: deadlock without terminating - but allow time to pass *)
| "step_cyphyaction timestep n t s astStop = Some [Timestep s False astStop]"
  (* Chaos: error out of checking *)
| "step_cyphyaction timestep n t s astChaos = None"
  (* Assume: error out of checking if condition is false, terminate if true (behave as Skip) *)
| "step_cyphyaction timestep n t s (astAssume pred) = (if pred s then Some [Termination False s] else None)"
  (* Evolve: terminate immediately if condition false, otherwise update according to solution and time passes *)
| "step_cyphyaction timestep n t s (astEvolve sol pred)
      = Some (if pred s then [Timestep (sol timestep s) True (astEvolve sol pred)] else [Termination False s] )"
  (* no event means checking fails - but time could still pass (and perhaps lead to termination) *)
| "step_cyphyaction timestep n [] s (astSyncPrefix e P) = Some [Timestep s False (astSyncPrefix e P)]"
  (* check if event is correct, also allow time to pass *)
| "step_cyphyaction timestep n (Visible te # t) s (astSyncPrefix e P)
    = (if fast_equal te (build\<^bsub>e\<^esub> ()) then Some [EventStep P, Timestep s False (astSyncPrefix e P)] else Some [Timestep s False (astSyncPrefix e P)] )"
  (* an event prefixing can't produce a hidden event, but does allow time to pass *)
| "step_cyphyaction timestep n (Hidden depth te # t) s (astSyncPrefix e P) = Some [Timestep s False (astSyncPrefix e P)]"
  (* no event means checking fails - but time could still pass (and perhaps lead to termination) *)
| "step_cyphyaction timestep n [] s (astEventPrefix e P) = Some [Timestep s False (astEventPrefix e P)]"
  (* check if event is correct, also allow time to pass *)
| "step_cyphyaction timestep n (Visible te # t) s (astEventPrefix e P)
    = (if fast_equal te e then Some [EventStep P, Timestep s False (astEventPrefix e P)] else Some [Timestep s False (astEventPrefix e P)] )"
  (* an event prefixing can't produce a hidden event, but does allow time to pass *)
| "step_cyphyaction timestep n (Hidden depth te # t) s (astEventPrefix e P) = Some [Timestep s False (astEventPrefix e P)]"
  (* no event means checking fails - but time could still pass (and perhaps lead to termination)*)
| "step_cyphyaction timestep n [] s (astOutputPrefix chexpr P) = Some [Timestep s False (astOutputPrefix chexpr P)]"
  (* check if event is correct, also allow time to pass *)
| "step_cyphyaction timestep n (Visible te # t) s (astOutputPrefix chexpr P)
    = (if fast_equal (chexpr s) te then Some [EventStep P, Timestep s False (astOutputPrefix chexpr P)] else Some [Timestep s False (astOutputPrefix chexpr P)] )"
  (* an output prefixing can't produce a hidden event, but does allow time to pass *)
| "step_cyphyaction timestep n (Hidden depth te # t) s (astOutputPrefix chexpr P) = Some [Timestep s False (astOutputPrefix chexpr P)]"
  (* no event means checking fails - but time could still pass (and perhaps lead to termination) *)
| "step_cyphyaction timestep n [] s (astInputPrefix F e) = Some [Timestep s False (astInputPrefix F e)]"
  (* check if event is correct, also allow time to pass *)
| "step_cyphyaction timestep n (Visible te # t) s (astInputPrefix F e)
    = (case F te of
          None \<Rightarrow> Some [Timestep s False (astInputPrefix F e)] \<comment> \<open>event not valid, deadlock\<close>
        | Some (pred, P) \<Rightarrow> \<comment> \<open>event is valid, but is the predicate true?\<close>
            if pred s then
              Some [EventStep P, Timestep s False (astInputPrefix F e)]
            else
              Some [Timestep s False (astInputPrefix F e)] \<comment> \<open> we can wait until the predicate is true \<close> )"
  (* input prefixing cannot produce a hidden event - but time could still pass *)
| "step_cyphyaction timestep n (Hidden depth te # t) s (astInputPrefix F e) = Some [Timestep s False (astInputPrefix F e)]"
  (* try the first, then proceed to the second after termination *)
| "step_cyphyaction timestep n t s (astSeq P Q) =
      (case (step_cyphyaction timestep n t s P) of
          Some xs \<Rightarrow>
            Some (map
              (\<lambda> step. case step of
                  Termination b s' \<Rightarrow> StUpd s' b Q
                | Timestep s' strict P' \<Rightarrow> Timestep s' strict (astSeq P' Q)
                | StUpd s' b P' \<Rightarrow> StUpd s' b (astSeq P' Q)
                | EventStep P' \<Rightarrow> EventStep (astSeq P' Q))
              xs)
        | None \<Rightarrow> None)"
  (* deadlock if predicate is false, otherwise behave as inner action*)
| "step_cyphyaction timestep n t s (astGuard pred P)
      = (if pred s then step_cyphyaction timestep n t s P else Some [Timestep s False astStop] )"
  (* behave as either inner action depending on predicate*)
| "step_cyphyaction timestep n t s (astCond pred P Q)
      = (if pred s then step_cyphyaction timestep n t s P else step_cyphyaction timestep n t s Q)"
  (* terminate immediately if the predicate is true, otherwise continue the inner action without resolving the interrupt *)
| "step_cyphyaction timestep n t s (astInterruptCond P pred) =
    (if pred s then
        Some [Termination False s]
      else
        map_option
          (map (map_cyphystep_continuation (\<lambda>P'. astInterruptCond P' pred)))
          (step_cyphyaction timestep n t s P))"
  (* behave as Q if the deadline has expires is true, otherwise continue P without, reducing the deadline *)
| "step_cyphyaction timestep n t s (astTimeout P sn Q) =
      (if fast_equal (sn s) 0 then
        step_cyphyaction timestep n t s Q
      else
        map_option
          (map (map_cyphystep_continuation (\<lambda>P'. astTimeout P' (\<lambda>s. sn s - timestep) Q)))
          (step_cyphyaction timestep n t s P))"
  (* evaluate both and concatenate results *)
| "step_cyphyaction timestep n t s (astIntChoice P Q)
      = (case (step_cyphyaction timestep n t s P, step_cyphyaction timestep n t s Q) of
          (Some xs, Some ys) \<Rightarrow> Some (map make_strict_internal (xs @ ys))
        | _ \<Rightarrow> None)"
  (* synchronise timesteps, concatenate choices *)
| "step_cyphyaction timestep n t s (astExtChoice P Q)
      = (case (step_cyphyaction timestep n t s P, step_cyphyaction timestep n t s Q) of
          (Some xs, Some ys) \<Rightarrow>
            \<comment> \<open>a timestep that doesn't change the state doesn't resolve the choice\<close>
            Some (case (List.partition (\<lambda> step. case step of Timestep s' strict _ \<Rightarrow> fast_equal s' s | _ \<Rightarrow> False) xs,
                        List.partition (\<lambda> step. case step of Timestep s' strict _ \<Rightarrow> fast_equal s' s | _ \<Rightarrow> False) ys) of
              ((xs_ts, xs), (ys_ts, ys)) \<Rightarrow>
               (map make_strict_internal (xs @ ys)) @
                \<comment> \<open>merge timesteps\<close>
                (map
                  (\<lambda> (x, y). case (x, y) of (Timestep _ strict1 P', Timestep _ strict2 Q') \<Rightarrow>
                    Timestep s (disj strict1 strict2) (astExtChoice P' Q'))
                  (List.product xs_ts ys_ts)))
        | _ \<Rightarrow> None \<comment> \<open>if either side diverges, the whole thing does\<close>)"
  (* no event to merge, synchronise timesteps and termination *)
| "step_cyphyaction timestep n [] s (astParallelAct mrg cs P Q)
      = (case (map_option group_cyphysteps (step_cyphyaction timestep n [] s P),
                map_option group_cyphysteps (step_cyphyaction timestep n [] s Q)) of
              (Some (P_terms, P_timesteps, P_stupds, P_eventsteps),
                Some (Q_terms, Q_timesteps, Q_stupds, Q_eventsteps)) \<Rightarrow>
                        Some (
                          \<comment> \<open>unsynchronised steps evolve one side, merging the state\<close>
                          (map (\<lambda> P'. EventStep (astParallelAct mrg cs P' Q)) P_eventsteps)
                          @ (map (\<lambda> Q'. EventStep (astParallelAct mrg cs P Q')) Q_eventsteps)
                          @ (map (\<lambda> (s', b, P'). StUpd (mrg s s' s) b (astParallelAct mrg cs P' Q)) P_stupds)
                          @ (map (\<lambda> (s', b, Q'). StUpd (mrg s s s') b (astParallelAct mrg cs P Q')) Q_stupds)
                          \<comment> \<open>terminations are synchronised, merging the state\<close>
                          @ (map (\<lambda>((b1, s1), (b2, s2)). Termination (b1 \<and> b2) (mrg s s1 s2)) (List.product P_terms Q_terms))
                          \<comment> \<open>timesteps are synchronised, merging the state\<close>
                          @ (map (\<lambda>((s1, strict1, P'), (s2, strict2, Q')). 
                                Timestep (mrg s s1 s2) (disj strict1 strict2) (astParallelAct mrg cs P' Q'))
                              (List.product P_timesteps Q_timesteps))
                          \<comment> \<open>timesteps can synchronise with a termination, merging the state\<close>
                          @ (map (\<lambda>((s1, strict1, P'), (_, s2)). 
                                Timestep (mrg s s1 s2) strict1 (astParallelAct mrg cs P' astSkip))
                              (List.product P_timesteps Q_terms))
                          @ (map (\<lambda>((_, s1), (s2, strict2, Q')). 
                                Timestep (mrg s s1 s2) strict2 (astParallelAct mrg cs astSkip Q'))
                              (List.product P_terms Q_timesteps)))
            | _ \<Rightarrow> None \<comment> \<open>if either side diverges, the whole thing does\<close>)"
  (* hidden events are unsynchronised, synchronise timesteps and termination *)
| "step_cyphyaction timestep n (Hidden depth te # t) s (astParallelAct mrg cs P Q)
      = (case (map_option group_cyphysteps (step_cyphyaction timestep n (Hidden depth te # t) s P),
                map_option group_cyphysteps (step_cyphyaction timestep n (Hidden depth te # t) s Q)) of
              (Some (P_terms, P_timesteps, P_stupds, P_eventsteps),
                Some (Q_terms, Q_timesteps, Q_stupds, Q_eventsteps)) \<Rightarrow>
                        Some (
                          \<comment> \<open>unsynchronised steps evolve one side, merging the state\<close>
                          (map (\<lambda> P'. EventStep (astParallelAct mrg cs P' Q)) P_eventsteps)
                          @ (map (\<lambda> Q'. EventStep (astParallelAct mrg cs P Q')) Q_eventsteps)
                          @ (map (\<lambda> (s', b, P'). StUpd (mrg s s' s) b (astParallelAct mrg cs P' Q)) P_stupds)
                          @ (map (\<lambda> (s', b, Q'). StUpd (mrg s s s') b (astParallelAct mrg cs P Q')) Q_stupds)
                          \<comment> \<open>terminations are synchronised, merging the state\<close>
                          @ (map (\<lambda>((b1, s1), (b2, s2)). Termination (b1 \<and> b2) (mrg s s1 s2)) (List.product P_terms Q_terms))
                          \<comment> \<open>timesteps are synchronised, merging the state\<close>
                          @ (map (\<lambda>((s1, strict1, P'), (s2, strict2, Q')). 
                                Timestep (mrg s s1 s2) (disj strict1 strict2) (astParallelAct mrg cs P' Q'))
                              (List.product P_timesteps Q_timesteps))
                          \<comment> \<open>timesteps can synchronise with a termination, merging the state\<close>
                          @ (map (\<lambda>((s1, strict1, P'), (_, s2)). 
                                Timestep (mrg s s1 s2) strict1 (astParallelAct mrg cs P' astSkip))
                              (List.product P_timesteps Q_terms))
                          @ (map (\<lambda>((_, s1), (s2, strict2, Q')). 
                                Timestep (mrg s s1 s2) strict2 (astParallelAct mrg cs astSkip Q'))
                              (List.product P_terms Q_timesteps)))
            | _ \<Rightarrow> None \<comment> \<open>if either side diverges, the whole thing does\<close>)"
  (* visible events are handled depending on the synchronisation set, synchronise timesteps and termination *)
| "step_cyphyaction timestep n (Visible te # t) s (astParallelAct mrg cs P Q)
      = (case (map_option group_cyphysteps (step_cyphyaction timestep n (Visible te # t) s P),
                map_option group_cyphysteps (step_cyphyaction timestep n (Visible te # t) s Q)) of
              (Some (P_terms, P_timesteps, P_stupds, P_eventsteps),
                Some (Q_terms, Q_timesteps, Q_stupds, Q_eventsteps)) \<Rightarrow>
                        Some (
                          \<comment> \<open>check for whether we need to synchronise the event steps\<close>
                          (if fast_member te cs then
                            map (\<lambda> (P', Q'). EventStep (astParallelAct mrg cs P' Q')) (List.product P_eventsteps Q_eventsteps)
                          else
                            (map (\<lambda> P'. EventStep (astParallelAct mrg cs P' Q)) P_eventsteps)
                            @ (map (\<lambda> Q'. EventStep (astParallelAct mrg cs P Q')) Q_eventsteps))
                          \<comment> \<open>unsynchronised steps evolve one side, merging the state\<close>
                          @ (map (\<lambda> (s', b, P'). StUpd (mrg s s' s) b (astParallelAct mrg cs P' Q)) P_stupds)
                          @ (map (\<lambda> (s', b, Q'). StUpd (mrg s s s') b (astParallelAct mrg cs P Q')) Q_stupds)
                          \<comment> \<open>terminations are synchronised, merging the state\<close>
                          @ (map (\<lambda>((b1, s1), (b2, s2)). Termination (b1 \<and> b2) (mrg s s1 s2)) (List.product P_terms Q_terms))
                          \<comment> \<open>timesteps are synchronised, merging the state\<close>
                          @ (map (\<lambda>((s1, strict1, P'), (s2, strict2, Q')). 
                                Timestep (mrg s s1 s2) (disj strict1 strict2) (astParallelAct mrg cs P' Q'))
                              (List.product P_timesteps Q_timesteps))
                          \<comment> \<open>timesteps can synchronise with a termination, merging the state\<close>
                          @ (map (\<lambda>((s1, strict1, P'), (_, s2)). 
                                Timestep (mrg s s1 s2) strict1 (astParallelAct mrg cs P' astSkip))
                              (List.product P_timesteps Q_terms))
                          @ (map (\<lambda>((_, s1), (s2, strict2, Q')). 
                                Timestep (mrg s s1 s2) strict2 (astParallelAct mrg cs astSkip Q'))
                              (List.product P_terms Q_timesteps)))
            | _ \<Rightarrow> None \<comment> \<open>if either side diverges, the whole thing does\<close>)"
  (* unroll the loop at least enough to match the trace *)
| "step_cyphyaction timestep n t s (astRec m FF) = step_cyphyaction timestep n t s (FF (m * n))"
  (* if there are no events in the trace, just ignore hiding *)
| "step_cyphyaction timestep n [] s (astHide P S)
      = map_option (map (map_cyphystep_continuation (\<lambda>P. astHide P S))) (step_cyphyaction timestep n [] s P)"
  (* visible events in the hidden set can't happen under the hiding *)
| "step_cyphyaction timestep n (Visible te # t) s (astHide P S)
      = map_option (map (map_cyphystep_continuation (\<lambda>P. astHide P S))) 
          (if fast_member te S then 
            map_option (filter (Not \<circ> is_EventStep)) (step_cyphyaction timestep n (Visible te # t) s P)
          else
            step_cyphyaction timestep n (Visible te # t) s P)"
  (* hidden events in the hidden set are made visible - if they occur they need to be hidden again *)
| "step_cyphyaction timestep n (Hidden depth te # t) s (astHide P S)
      = map_option (map (map_cyphystep_continuation (\<lambda>P. astHide P S)))
          (if fast_member te S then
            case depth of
              0 \<Rightarrow> step_cyphyaction timestep n (Visible te # t) s P
            | Suc depth \<Rightarrow> step_cyphyaction timestep n (Hidden depth te # t) s P
        else
          step_cyphyaction timestep n (Hidden depth te # t) s P)"
  (* if there are no events in the trace, just ignore renaming *)
| "step_cyphyaction timestep n [] s (astRename (rel::'e \<leftrightarrow> 'e) P)
      = map_option (map (map_cyphystep_continuation (astRename rel))) (step_cyphyaction timestep n [] s P)"
  (* a hidden event can't be renamed *)
| "step_cyphyaction timestep n (Hidden depth te # t) s (astRename (rel::'e \<leftrightarrow> 'e) P)
      = map_option (map (map_cyphystep_continuation (astRename rel))) (step_cyphyaction timestep n (Hidden depth te # t) s P)"
  (* a visible event is reverse-renamed and then renamed back in the result *)
| "step_cyphyaction timestep n (Visible te # t) s (astRename rel P)
      = map_option (map (map_cyphystep_continuation (astRename rel))) 
          (if can_select (\<lambda>p. fast_equal te (snd p)) rel then
            fold (\<lambda>te'. combine_options (@) (step_cyphyaction timestep n (Visible te' # t) s P))
              (rapply_alist (the (set_to_list rel)) te)
              None
        else
          step_cyphyaction timestep n (Visible te # t) s P)"
  by (pat_completeness, auto)
termination
  by (relation "measures [\<lambda>(ts, n, t, s, ast). rec_depth n ast, \<lambda>(ts, n, t, s, ast). if ast = astSkip then 0 else 1 + size ast]")
    (auto simp add: mult.commute)

term step_cyphyaction
value "step_cyphyaction :: \<real> \<Rightarrow> \<nat> \<Rightarrow> nat visibility list \<Rightarrow> nat \<Rightarrow> (nat, nat) cyphyast \<Rightarrow> (nat, nat) cyphystep list option"

section \<open>Predicting the initial events that can be performed by a CyPhyCircus action\<close>

fun merge_known_initials :: "'e set \<Rightarrow> 'e visibility list \<times> (('e \<Rightarrow> bool) \<times> 'e) list \<Rightarrow> 'e visibility list \<times> (('e \<Rightarrow> bool) \<times> 'e) list \<Rightarrow> 'e visibility list" where
  "merge_known_initials cs ([], uks1) ([], uks2) = []"
| "merge_known_initials cs (Visible e # ks1, uks1) (ks2, uks2) =
    (if fast_member e cs then \<comment> \<open>does the event require synchronisation?\<close>
      if List.member ks2 (Visible e) then \<comment> \<open>if yes, is there a known event to synchronise with?\<close>
        [Visible e]
      else
        if list_ex (\<lambda> (f, _). f e) uks2 then \<comment> \<open>otherwise, is there an unknown event to synchronise with?\<close>
          [Visible e]
        else
          []
    else
      [Visible e] ) @ merge_known_initials cs (ks1, uks1) (ks2, uks2)"
| "merge_known_initials cs (Hidden n e # ks1, uks1) (ks2, uks2) = Hidden n e # merge_known_initials cs (ks1, uks1) (ks2, uks2)"
| "merge_known_initials cs ([], uks1) (Visible e # ks2, uks2) =
    (if fast_member e cs then \<comment> \<open>does the event require synchronisation?\<close>
        if list_ex (\<lambda> (f, _). f e) uks1 then \<comment> \<open>if yes, is there an unknown event to synchronise with? (no known events to check)\<close>
          [Visible e]
        else
          []
    else
      [Visible e] ) @ merge_known_initials cs ([], uks1) (ks2, uks2)"
| "merge_known_initials cs ([], uks1) (Hidden n e # ks2, uks2) = Hidden n e # merge_known_initials cs ([], uks1) (ks2, uks2)"

fun merge_unknown_initials :: "'e set \<Rightarrow> 'e visibility list \<times> (('e \<Rightarrow> bool) \<times> 'e) list \<Rightarrow> 'e visibility list \<times> (('e \<Rightarrow> bool) \<times> 'e) list \<Rightarrow> (('e \<Rightarrow> bool) \<times> 'e) list" where
  "merge_unknown_initials cs (ks1, []) (ks2, []) = []"
| "merge_unknown_initials cs (ks1, (f, re) # uks1) (ks2, uks2) =
    (if fast_member re cs then  \<comment> \<open>do the events require synchronisation?\<close>
      if list_ex (case_visibility f (\<lambda>_ _. False)) ks2 then  \<comment> \<open>if yes, is there a visible known event that it can synchronise with\<close>
        [] \<comment> \<open>if yes, then it becomes known and leaves the unknown list\<close>
      else
         \<comment> \<open>if no, merge it with those in uks2 that haven't synchronised with a known event\<close>
        List.map_filter (\<lambda>(f2, re2). if f re2 then Some (\<lambda> e. f e \<and> f2 e, re) else if f2 re then Some (\<lambda> e. f e \<and> f2 e, re2) else None)
          (filter (\<lambda> (f2, _). Not (list_ex (case_visibility f2 (\<lambda>_ _. False)) ks1)) uks2)
    else
      [(f, re)] ) @ merge_unknown_initials cs (ks1, uks1) (ks2, uks2)"
| "merge_unknown_initials cs (ks1, []) (ks2, (f, re) # uks2) =
    (if fast_member re cs then  \<comment> \<open>do the events require synchronisation?\<close>
      [] \<comment> \<open>if yes, either there a visible known event that it can synchronise with, or it has already been merged with uks1\<close>
    else
      [(f, re)] ) @ merge_unknown_initials cs (ks1, []) (ks2, uks2)"

fun rename_events :: "('e \<times> 'e) list \<Rightarrow> 'e visibility list \<Rightarrow> 'e visibility list" where
  "rename_events alist [] = []"
| "rename_events alist (Visible e # xs) =
    (case_list [Visible e] (#) (List.map_filter (\<lambda>(a,b). if fast_equal a e then Some (Visible b) else None) alist)) @ rename_events alist xs"
| "rename_events alist (Hidden n e # xs) = Hidden n e # rename_events alist xs"

function (sequential) initial_events' :: "real \<Rightarrow> nat \<Rightarrow> ('e, 's) cyphyast \<Rightarrow> 's \<Rightarrow> 'e visibility list \<times> (('e \<Rightarrow> bool) \<times> 'e) list \<times> (('e \<Rightarrow> bool) \<times> 'e) list  \<times> 's option" where
  "initial_events' ts n astSkip s = ([], [], [], Some s)"
| "initial_events' ts n (astAssigns subst) s = ([], [], [], Some (subst s))"
| "initial_events' ts n astStop s = ([], [], [], None)"
| "initial_events' ts n astChaos s = ([], [], [], None)"
| "initial_events' ts n (astAssume pred) s = ([], [], [], if pred s then Some s else None)"
| "initial_events' ts n (astEvolve f pred) s = ([], [], [], Some (if pred s then s else f ts s))"
| "initial_events' ts n (astSyncPrefix e P) s = ([Visible (build\<^bsub>e\<^esub> ())], [], [], None)"
| "initial_events' ts n (astEventPrefix e P) s = ([Visible e], [], [], None)"
| "initial_events' ts n (astOutputPrefix f P) s = ([Visible (f s)], [], [], None)"
| "initial_events' ts n (astInputPrefix F re) s = ([], [(\<lambda>e. (Not o Option.is_none o F) e, re)], [], None)"
| "initial_events' ts n (astSeq P Q) s =
    (case initial_events' ts n P s of
        (_, _, _, Some s) \<Rightarrow> initial_events' ts n Q s
      | r \<Rightarrow> r)"
| "initial_events' ts n (astGuard pred P) s = (if pred s then initial_events' ts n P s else ([], [], [], None))"
| "initial_events' ts n (astCond pred P Q) s = (if pred s then initial_events' ts n P s else initial_events' ts n Q s)"
| "initial_events' ts n (astIntChoice P Q) s =
  (case (initial_events' ts n P s, initial_events' ts n Q s) of
      ((knowns1, unknowns1, hiddens1, _), (knowns2, unknowns2, hiddens2, _)) \<Rightarrow> (knowns1 @ knowns2, unknowns1 @ unknowns2, hiddens1 @ hiddens2, None))"
| "initial_events' ts n (astExtChoice P Q) s =
  (case (initial_events' ts n P s, initial_events' ts n Q s) of
      ((knowns1, unknowns1, hiddens1, _), (knowns2, unknowns2, hiddens2, _)) \<Rightarrow> (knowns1 @ knowns2, unknowns1 @ unknowns2, hiddens1 @ hiddens2, None))"
| "initial_events' ts n (astParallelAct mrg cs P Q) s =
  (case (initial_events' ts n P s, initial_events' ts n Q s) of
      ((ks1, uks1, hs1, opt1), (ks2, uks2, hs2, opt2)) \<Rightarrow>
        (merge_known_initials cs (ks1, uks1) (ks2, uks2),
          merge_unknown_initials cs (ks1, uks1) (ks2, uks2),
          hs1 @ hs2,
          case (opt1, opt2) of (Some s1, Some s2) \<Rightarrow> Some (mrg s s1 s2) | _ \<Rightarrow> None))"
| "initial_events' ts n (astRec m F) s = initial_events' ts n (F m) s"
| "initial_events' ts n (astHide P S) s =
    (case initial_events' ts n P s of
        (knowns, unknowns, hiddens, opt) \<Rightarrow>
          (map (case_visibility (\<lambda>e. if fast_member e S then Hidden 0 e else Visible e) (\<lambda>n e. if fast_member e S then Hidden (n+1) e else Hidden n e)) knowns,
            filter (\<lambda>(f, re). Not (fast_member re S)) unknowns,
            filter (\<lambda>(f, re). fast_member re S) unknowns @ hiddens,
            opt))"
| "initial_events' ts n (astRename f P) s =
    (case initial_events' ts n P s of
        (knowns, unknowns, hiddens, opt) \<Rightarrow>
          (rename_events (the (set_to_list f)) knowns,
            map (\<lambda>(g, re).
              (\<lambda> x. List.list_all (g o (case_visibility id (\<lambda>_. id))) (rename_events (the (set_to_list f)) [Visible x] ),
                case_option re snd (List.find (\<lambda>(x,y). fast_equal x re) (the (set_to_list f))))) unknowns,
            hiddens,
            opt))"
| "initial_events' ts n (astInterruptCond P pred) s = (if pred s then ([], [], [], None) else initial_events' ts n P s)"
| "initial_events' ts n (astTimeout P f Q) s =
    (if f s \<le> 0 then
      initial_events' ts n Q s
    else
      case initial_events' ts n P s of
          (ks, uks, hs, Some s') \<Rightarrow> initial_events' ts n Q s'
        | (ks, uks, hs, None) \<Rightarrow> (ks, uks, hs, None))"
  by (pat_completeness, auto)
termination
  by (relation "measures [\<lambda>(ts, n, ast, s). rec_depth 1 ast, \<lambda>(ts, n, ast, s). size ast]", auto simp add: mult.commute)

definition initial_events_to_try :: "real \<Rightarrow> nat \<Rightarrow> ('e, 's) cyphyast \<Rightarrow> 's \<Rightarrow> 'e visibility list option" where
  "initial_events_to_try ts n P s =
    (case initial_events' ts n P s of
        (ks, _, [], _) \<Rightarrow> Some ks
      | (ks, _, x#xs, _) \<Rightarrow> None)"

definition hidden_initial_events_to_try :: "real \<Rightarrow> nat \<Rightarrow> ('e, 's) cyphyast \<Rightarrow> 's \<Rightarrow> 'e visibility list option" where
  "hidden_initial_events_to_try ts n P s =
    map_option (filter (case_visibility (\<lambda>_. False) (\<lambda>_ _. True))) (initial_events_to_try ts n P s)"

section \<open>Lifting the operational semantics to trace checking\<close>

fun expand_cyphyaction_step_immediate :: "'e visibility list \<Rightarrow> 's \<Rightarrow> ('e, 's) cyphystep list \<Rightarrow> ('s \<times> 'e visibility list \<times> ('e, 's) cyphyast option) list \<Rightarrow> ('s \<times> 'e visibility list \<times> ('e, 's) cyphyast option) list" where
  "expand_cyphyaction_step_immediate t s [] acc = acc"
| "expand_cyphyaction_step_immediate t s (Termination _ s' # steps) acc = expand_cyphyaction_step_immediate t s steps ((s', t, None) # acc)"
| "expand_cyphyaction_step_immediate t s (Timestep s' _ P # steps) acc = expand_cyphyaction_step_immediate t s steps acc"
| "expand_cyphyaction_step_immediate t s (StUpd s' True P # steps) acc = expand_cyphyaction_step_immediate t s steps ((s', t, Some P) # acc)"
| "expand_cyphyaction_step_immediate t s (StUpd s' False P # steps) acc = expand_cyphyaction_step_immediate t s steps acc"
| "expand_cyphyaction_step_immediate t s (EventStep P # steps) acc = expand_cyphyaction_step_immediate t s steps acc"

fun expand_cyphyaction_step_acc :: "'e visibility list \<Rightarrow> 's \<Rightarrow> ('e, 's) cyphystep list \<Rightarrow> ('s \<times> 'e visibility list \<times> ('e, 's) cyphyast option) list \<Rightarrow> ('s \<times> 'e visibility list \<times> ('e, 's) cyphyast option) list" where
  "expand_cyphyaction_step_acc t s [] acc = acc"
| "expand_cyphyaction_step_acc t s (Termination b s' # steps) acc = expand_cyphyaction_step_immediate t s steps [(s', t, None)]"
| "expand_cyphyaction_step_acc t s (Timestep s' False P # steps) acc = expand_cyphyaction_step_acc t s steps acc"
| "expand_cyphyaction_step_acc t s (Timestep s' True P # steps) acc = expand_cyphyaction_step_acc t s steps ((s', t, Some P) # acc)"
| "expand_cyphyaction_step_acc t s (StUpd s' b P # steps) acc = expand_cyphyaction_step_immediate t s steps [(s', t, Some P)]"
| "expand_cyphyaction_step_acc t s (EventStep P # steps) acc = expand_cyphyaction_step_acc t s steps ((s, tl t, Some P) # acc)"

definition expand_cyphyaction_step :: "'e visibility list \<Rightarrow> 's \<Rightarrow> ('e, 's) cyphystep list \<Rightarrow> ('s \<times> 'e visibility list \<times> ('e, 's) cyphyast option) list" where
  "expand_cyphyaction_step t s steps = expand_cyphyaction_step_acc t s steps []"

fun lift_cyphyaction_step :: "nat \<Rightarrow> real \<Rightarrow>
      ('s \<times> 'e visibility list \<times> ('e, 's) cyphyast option)
        \<Rightarrow> ('s \<times> 'e visibility list \<times> ('e, 's) cyphyast option) list option" where
  "lift_cyphyaction_step n ts (s, t, None) = Some [(s, t, None)]"
| "lift_cyphyaction_step n ts (s, t, Some P) = map_option (expand_cyphyaction_step t s) (step_cyphyaction ts n t s P)"

fun option_list_bind :: "'a list option \<Rightarrow> ('a \<Rightarrow> 'b list option) \<Rightarrow> 'b list option" where
  "option_list_bind None f = None"
| "option_list_bind (Some []) f = Some []"
| "option_list_bind (Some [x] ) f = f x"
| "option_list_bind (Some (x # xs)) f = combine_options (@) (f x) (option_list_bind (Some xs) f)"

fun advance_cyphyaction :: "nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> ('s \<times> ('e, 's) cyphyast option)
        \<Rightarrow> ('s \<times> ('e, 's) cyphyast option) list option" where
  "advance_cyphyaction n unroll ts (s, None) = Some [(s, None)]"
| "advance_cyphyaction n unroll ts (s, Some P) =
    (if n = 0 then
      None
    else
      case lift_cyphyaction_step unroll ts (s, [], Some P) of
          None \<Rightarrow> None
        | Some [] \<Rightarrow> Some [(s, Some P)] 
        | a \<Rightarrow> option_list_bind a (\<lambda>(x, _, y) \<Rightarrow> advance_cyphyaction (n-1) unroll ts (x, y)))"

(* checks through a trace, returning continuations if it has the trace, empty trace if not, None on divergence *)
fun cyphyaction_check_trace :: "nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> bool \<Rightarrow> ('s \<times> 'e visibility list \<times> ('e, 's) cyphyast option)
        \<Rightarrow> ('s \<times> ('e, 's) cyphyast option) list option" where
  "cyphyaction_check_trace n unroll ts False (s, [], P_opt) = Some [(s, P_opt)]" (* everything has the empty trace *)
| "cyphyaction_check_trace n unroll ts True (s, [], None) = Some [(s, None)]" (* a terminating process has a trace that is just tick *)
| "cyphyaction_check_trace n unroll ts has_tick (s, e # t, None) = Some []" (* a terminating process can't do more events *)
| "cyphyaction_check_trace n unroll ts has_tick (s, t, Some P) =
    (if n = 0 then
      None
    else
     option_list_bind
      (lift_cyphyaction_step unroll ts (s, t, Some P))
      (cyphyaction_check_trace (n-1) unroll ts has_tick))" (* if there is a next process, explore it *)

fun cyphyaction_check_try_events' :: "nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> bool \<Rightarrow> ('s \<times>  ('e, 's) cyphyast option) \<Rightarrow> 'e visibility list
        \<Rightarrow> ('s \<times> ('e, 's) cyphyast option) list option" where
  "cyphyaction_check_try_events' n unroll ts has_tick (s, P_opt) evs =
    (if List.null evs then
      Some []
    else
      fold (\<lambda> e steps. combine_options (@) (cyphyaction_check_trace n unroll ts has_tick (s, [e], P_opt)) steps) evs None)"

fun cyphyaction_check_try_hidden_events :: "nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> bool \<Rightarrow> ('s \<times>  ('e, 's) cyphyast option)
        \<Rightarrow> ('s \<times> ('e, 's) cyphyast option) list option option" where
  "cyphyaction_check_try_hidden_events n unroll ts False (s, None) = Some (Some [])" (* a terminating process can't do more events *)
| "cyphyaction_check_try_hidden_events n unroll ts True (s, None) = Some (Some [(s, None)] )" (* a terminating process has a trace that is just tick *)
| "cyphyaction_check_try_hidden_events n unroll ts has_tick (s, Some P) =
    map_option (cyphyaction_check_try_events' n unroll ts has_tick (s, Some P)) (hidden_initial_events_to_try ts unroll P s)"

fun cyphyaction_check_visible_trace_inferred :: "nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> bool \<Rightarrow> 'e list \<Rightarrow> 's \<times> ('e, 's) cyphyast option \<Rightarrow> ('s \<times> ('e, 's) cyphyast option) list option option" where
  "cyphyaction_check_visible_trace_inferred n unroll ts False [] (s, P_opt) = Some (Some [(s, P_opt)] )" (* everything has the empty trace *)
| "cyphyaction_check_visible_trace_inferred n unroll ts True [] (s, None) = Some (Some [(s, None)] )" (* a terminating process has a trace that is just tick *)
| "cyphyaction_check_visible_trace_inferred n unroll ts has_tick (e#t) (s, None) = Some (Some [] )" (* a terminating process can't do more events *)
| "cyphyaction_check_visible_trace_inferred n unroll ts True [] (s, Some P) = 
    (case cyphyaction_check_trace n unroll ts True (s, [], Some P) of
        None \<Rightarrow>  Some None \<comment> \<open>divergence\<close>
      | Some (step#steps) \<Rightarrow> Some (Some (step#steps)) \<comment> \<open>termination succeeded, return steps\<close>
      | Some [] \<Rightarrow> \<comment> \<open>termination failed, try a hidden event\<close>
          (case cyphyaction_check_try_hidden_events n unroll ts False (s, Some P) of
            None \<Rightarrow> None \<comment> \<open>hidden events couldn't be determined\<close>
          | Some None \<Rightarrow> Some None \<comment> \<open>divergence\<close>
          | Some (Some []) \<Rightarrow> Some (Some []) \<comment> \<open>no hidden events possible\<close>
          | Some (Some (step#steps)) \<Rightarrow> \<comment> \<open>hidden events occurred, try next steps\<close>
              (map_option (map_option concat o those) o those o map (cyphyaction_check_visible_trace_inferred (n - 1) unroll ts True [])) (step#steps)))"
| "cyphyaction_check_visible_trace_inferred n unroll ts has_tick (e#t) (s, Some P) =
    (if n = 0 then Some None else
      case cyphyaction_check_trace n unroll ts False (s, [Visible e], Some P) of
        None \<Rightarrow> Some None \<comment> \<open>divergence \<close>
      | Some (step#steps) \<Rightarrow> (map_option (map_option concat o those) o those o map (cyphyaction_check_visible_trace_inferred n unroll ts has_tick t)) (step#steps) \<comment> \<open>visible step succeeded, try the next event \<close>
      | Some [] \<Rightarrow> \<comment> \<open>visible step failed, try a hidden event\<close>
          (case cyphyaction_check_try_hidden_events n unroll ts False (s, Some P) of
            None \<Rightarrow> None \<comment> \<open>hidden events couldn't be determined\<close>
          | Some None \<Rightarrow> Some None \<comment> \<open>divergence \<close>
          | Some (Some []) \<Rightarrow> Some (Some []) \<comment> \<open>no hidden events possible\<close>
          | Some (Some (step#steps)) \<Rightarrow>\<comment> \<open>hidden events occurred, try next steps\<close>
              (map_option (map_option concat o those) o those o map (cyphyaction_check_visible_trace_inferred (n - 1) unroll ts has_tick (e#t))) (step#steps)))"

(*fun cyphyaction_check_visible_trace_inferred :: "nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> bool \<Rightarrow> 'e list \<Rightarrow> 's \<times> ('e, 's) cyphyast option \<Rightarrow> ('s \<times> ('e, 's) cyphyast option) list option option" where
  "cyphyaction_check_visible_trace_inferred n unroll ts False [] (s, P_opt) = Some (Some [(s, P_opt)] )" (* everything has the empty trace *)
| "cyphyaction_check_visible_trace_inferred n unroll ts True [] (s, None) = Some (Some [(s, None)] )" (* a terminating process has a trace that is just tick *)
| "cyphyaction_check_visible_trace_inferred n unroll ts has_tick (e#t) (s, None) = Some (Some [] )" (* a terminating process can't do more events *)
| "cyphyaction_check_visible_trace_inferred n unroll ts True [] (s, Some P) = 
    (case advance_cyphyaction n unroll ts (s, Some P) of
        None \<Rightarrow>  Some None \<comment> \<open>divergence\<close>
      | Some steps \<Rightarrow>  \<comment> \<open>got steps - are any termination?\<close>
          if list_ex (Option.is_none o snd) steps then
            Some (Some (filter (Option.is_none o snd) steps))  \<comment> \<open>sucessfully terminated - return the termination steps\<close>
          else
            \<comment> \<open>failed to terminate - try a hidden event\<close>
            (case fold
                    (\<lambda>step res. combine_options (combine_options (@)) (cyphyaction_check_try_hidden_events n unroll ts False step) res)
                    (if List.null steps then [(s, Some P)] else steps)
                    None of
                  None \<Rightarrow> None \<comment> \<open>hidden events couldn't be determined\<close>
                | Some None \<Rightarrow> Some None \<comment> \<open>divergence\<close>
                | Some (Some []) \<Rightarrow> Some (Some []) \<comment> \<open>no hidden events possible\<close>
                | Some (Some (step#steps)) \<Rightarrow> \<comment> \<open>hidden events occurred, try next steps\<close>
                    (map_option (map_option concat o those) o those o map (cyphyaction_check_visible_trace_inferred (n - 1) unroll ts True [])) (step#steps))
              )"
| "cyphyaction_check_visible_trace_inferred n unroll ts has_tick (e#t) (s, Some P) =
    (if n = 0 then Some None else
      case advance_cyphyaction n unroll ts (s, Some P) of
        None \<Rightarrow>  Some None \<comment> \<open>divergence\<close>
      | Some steps \<Rightarrow>  \<comment> \<open>got steps - try starting from each\<close>
          fold (\<lambda>step res. combine_options (combine_options (@)) res
            (case cyphyaction_check_trace n unroll ts False (s, [Visible e], Some P) of
                None \<Rightarrow> Some None \<comment> \<open>divergence \<close>
              | Some (step#steps) \<Rightarrow> (map_option (map_option concat o those) o those o map (cyphyaction_check_visible_trace_inferred n unroll ts has_tick t)) (step#steps) \<comment> \<open>visible step succeeded, try the next event \<close>
              | Some [] \<Rightarrow> \<comment> \<open>visible step failed, try a hidden event\<close>
                  (case cyphyaction_check_try_hidden_events n unroll ts False (s, Some P) of
                    None \<Rightarrow> None \<comment> \<open>hidden events couldn't be determined\<close>
                  | Some None \<Rightarrow> Some None \<comment> \<open>divergence \<close>
                  | Some (Some []) \<Rightarrow> Some (Some []) \<comment> \<open>no hidden events possible\<close>
                  | Some (Some (step#steps)) \<Rightarrow>\<comment> \<open>hidden events occurred, try next steps\<close>
                      (map_option (map_option concat o those) o those o map (cyphyaction_check_visible_trace_inferred (n - 1) unroll ts has_tick (e#t))) (step#steps))))
            (if List.null steps then [(s, Some P)] else steps) None)"*)

fun cyphyaction_has_trace_incremental :: "nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> ('e, 's) cyphyast \<Rightarrow> 'e visibility list \<Rightarrow> bool \<Rightarrow> 's \<Rightarrow> ('e visibility list \<times> bool) option" where
  "cyphyaction_has_trace_incremental n unroll ts P [] False s = None"
| "cyphyaction_has_trace_incremental n unroll ts P [] True s = 
    (case cyphyaction_check_trace n unroll ts True (s, [], Some P) of
        None \<Rightarrow> Some ([], True) \<comment> \<open>divergence doesn't end in termination, produce a counterexample\<close>
      | Some [] \<Rightarrow> Some ([], True) \<comment> \<open>failed, produce a counterexample\<close>
      | Some (step#steps) \<Rightarrow> None) \<comment> \<open>succeeded\<close>" 
| "cyphyaction_has_trace_incremental n unroll ts P (e#t) has_tick s =
    (case cyphyaction_check_trace n unroll ts False (s, [e], Some P) of
      None \<Rightarrow> Some ([e], False) \<comment> \<open>divergence, start creating a counterexample\<close>
    | Some [] \<Rightarrow> \<comment> \<open>failed, start creating a counterexample\<close>
        Some ([e], False)
    | Some (step#steps) \<Rightarrow> \<comment> \<open>succeeded, try the next ones\<close>
        (map_option hd \<circ> those)
          (map (\<lambda>(s', opt_P').
            case opt_P' of
              None \<Rightarrow> Some ([e], False) \<comment> \<open>this branch terminated, but we had more to search for, start creating a counterexample\<close>
            | Some P' \<Rightarrow> map_option (apfst ((#) e)) (cyphyaction_has_trace_incremental n unroll ts P' t has_tick s'))
        (step#steps)))"

definition cyphyaction_has_trace_incremental' :: "nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> 'e visibility list \<Rightarrow> bool \<Rightarrow> 's \<Rightarrow> ('e visibility list \<times> bool) option" where
  "cyphyaction_has_trace_incremental' n unroll ts P t has_tick s = cyphyaction_has_trace_incremental n unroll ts (cyphyaction_to_cyphyast P) t has_tick s"

fun cyphyaction_has_visible_trace_incremental :: "nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> ('e, 's) cyphyast \<Rightarrow> 'e list \<Rightarrow> bool \<Rightarrow> 's \<Rightarrow> ('e list \<times> bool) option" where
  "cyphyaction_has_visible_trace_incremental n unroll ts P [] False s = None"
| "cyphyaction_has_visible_trace_incremental n unroll ts P [] True s = 
    (case cyphyaction_check_trace n unroll ts True (s, [], Some P) of
        None \<Rightarrow> Some ([], True) \<comment> \<open>divergence doesn't end in termination, produce a counterexample\<close>
      | Some [] \<Rightarrow> Some ([], True) \<comment> \<open>failed, produce a counterexample\<close>
      | Some (step#steps) \<Rightarrow> None)" \<comment> \<open>succeeded\<close>
| "cyphyaction_has_visible_trace_incremental n unroll ts P (e#t) has_tick s =
    (case cyphyaction_check_trace n unroll ts False (s, [Visible e], Some P) of
      None \<Rightarrow> Some ([e], False) \<comment> \<open>divergence, start creating a counterexample\<close>
    | Some [] \<Rightarrow> \<comment> \<open>failed, start creating a counterexample\<close>
        Some ([e], False)
    | Some (step#steps) \<Rightarrow> \<comment> \<open>succeeded, try the next ones\<close>
        (map_option hd \<circ> those)
          (map (\<lambda>(s', opt_P').
              case opt_P' of
                None \<Rightarrow> Some ([e], False) \<comment> \<open>this branch terminated, but we had more to search for, start creating a counterexample\<close>
              | Some P' \<Rightarrow> map_option (apfst ((#) e)) (cyphyaction_has_visible_trace_incremental n unroll ts P' t has_tick s'))
          (step#steps)))"

definition cyphyaction_has_visible_trace_incremental' :: "nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> 'e list \<Rightarrow> bool \<Rightarrow> 's \<Rightarrow> ('e list \<times> bool) option" where
  "cyphyaction_has_visible_trace_incremental' n unroll ts P t has_tick s = cyphyaction_has_visible_trace_incremental n unroll ts (cyphyaction_to_cyphyast P) t has_tick s"

fun try_list_opt :: "('a \<Rightarrow> 'b option option) \<Rightarrow> 'a list \<Rightarrow> 'b option option" where
  "try_list_opt f [] = Some None"
| "try_list_opt f (x#xs) =
    (case f x of
      Some (Some r) \<Rightarrow> Some (Some r)
    | Some None \<Rightarrow> try_list_opt f xs
    | None \<Rightarrow> None)"

fun cyphyaction_has_visible_trace_inferred_incremental :: "nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> ('e, 's) cyphyast \<Rightarrow> 'e list \<Rightarrow> bool \<Rightarrow> 's \<Rightarrow> ('e list \<times> bool) option option" where
  "cyphyaction_has_visible_trace_inferred_incremental n unroll ts P [] False s = Some None"
| "cyphyaction_has_visible_trace_inferred_incremental n unroll ts P [] True s = 
    (case cyphyaction_check_visible_trace_inferred n unroll ts True [] (s, Some P) of
        None \<Rightarrow> None \<comment> \<open>can't determine hidden events with certainty, fail out\<close>
      | Some None \<Rightarrow> Some (Some ([], True)) \<comment> \<open>divergence doesn't end in termination, produce a counterexample\<close>
      | Some (Some []) \<Rightarrow> Some (Some ([], True)) \<comment> \<open>failed, produce a counterexample\<close>
      | Some (Some (step#steps)) \<Rightarrow> Some None)" \<comment> \<open>succeeded with termination, no counterexample\<close>
| "cyphyaction_has_visible_trace_inferred_incremental n unroll ts P (e#t) has_tick s =
    (case cyphyaction_check_visible_trace_inferred n unroll ts False [e] (s, Some P) of
        None \<Rightarrow> None \<comment> \<open>can't determine hidden events with certainty, fail out\<close>
      | Some None \<Rightarrow> Some (Some ([e], False)) \<comment> \<open>divergence, produce a counterexample\<close>
      | Some (Some []) \<Rightarrow> Some (Some ([e], False)) \<comment> \<open>failed, produce a counterexample\<close>
      | Some (Some (step#steps)) \<Rightarrow> \<comment> \<open>succeeded, try the next steps\<close>
        try_list_opt
          (\<lambda>(s', opt_P').
              case opt_P' of
                None \<Rightarrow> Some (Some ([e], False)) \<comment> \<open>this branch terminated, but we had more to search for, start creating a counterexample\<close>
              | Some P' \<Rightarrow> map_option (map_option (apfst ((#) e))) (cyphyaction_has_visible_trace_inferred_incremental n unroll ts P' t has_tick s'))
          (step#steps))"

definition cyphyaction_has_visible_trace_inferred_incremental' :: "nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> 'e list \<Rightarrow> bool \<Rightarrow> 's \<Rightarrow> ('e list \<times> bool) option option" where
  "cyphyaction_has_visible_trace_inferred_incremental' n unroll ts P t has_tick s =
    cyphyaction_has_visible_trace_inferred_incremental n unroll ts (cyphyaction_to_cyphyast P) t has_tick s"

section \<open>Lifting the trace checking over constant instantiations\<close>

(* want to check that there exists an instantiation of the constants that makes P have the given trace *)

fun cyphyaction_has_trace_incremental_insts :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> (('a::full_exhaustive) \<Rightarrow> ('e, 's) cyphyast) \<Rightarrow> (('a::full_exhaustive) \<Rightarrow> bool) \<Rightarrow> 'e visibility list \<Rightarrow> bool \<Rightarrow> 's \<Rightarrow> 'e visibility list \<Rightarrow> ('e visibility list \<times> bool) option" where
  "cyphyaction_has_trace_incremental_insts step_limit breadth unroll ts P pred [] has_tick s to_check =
    (case full_exhaustive_class.full_exhaustive
        (\<lambda> (a, term).
          if pred a then
            case cyphyaction_has_trace_incremental step_limit unroll ts (P a) to_check has_tick s of
              None \<Rightarrow> Some (True, []) \<comment> \<open>the process has the trace, stop checking\<close>
            | Some _ \<Rightarrow> None \<comment> \<open>the process doesn't have the trace, continue\<close>
          else
            None)
        (natural_of_nat breadth) of
          Some _ \<Rightarrow> None \<comment> \<open>we have the trace, but we are at the end\<close>
        | None \<Rightarrow> Some (to_check, has_tick))" 
| "cyphyaction_has_trace_incremental_insts step_limit breadth unroll ts P pred (e#t) has_tick s to_check =
    (case full_exhaustive_class.full_exhaustive
        (\<lambda> (a, term).
          if pred a then
            case cyphyaction_has_trace_incremental step_limit unroll ts (P a) (to_check @ [e] ) has_tick s of
              None \<Rightarrow> Some (True, []) \<comment> \<open>the process has the trace, stop checking\<close>
            | Some _ \<Rightarrow> None \<comment> \<open>the process doesn't have the trace, continue\<close>
          else
            None)
        (natural_of_nat breadth) of
          Some _ \<Rightarrow> \<comment> \<open>we have the trace, try the next event\<close>
            cyphyaction_has_trace_incremental_insts step_limit breadth unroll ts P pred t has_tick s (to_check @ [e] )
        | None \<Rightarrow> Some (to_check, False))"

fun cyphyaction_has_trace_incremental_insts'
      :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> (('a::full_exhaustive) \<Rightarrow> ('e, 's) cyphyaction) \<Rightarrow> (('a::full_exhaustive) \<Rightarrow> bool) \<Rightarrow> 'e visibility list \<Rightarrow> bool \<Rightarrow> 's \<Rightarrow> 'e visibility list \<Rightarrow> ('e visibility list \<times> bool) option" where
  "cyphyaction_has_trace_incremental_insts' step_limit breadth unroll ts P pred t has_tick s to_check =
    cyphyaction_has_trace_incremental_insts step_limit breadth unroll ts (cyphyaction_to_cyphyast o P) pred t has_tick s to_check"

fun cyphyaction_has_visible_trace_incremental_insts
      :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> (('a::full_exhaustive) \<Rightarrow> ('e, 's) cyphyast) \<Rightarrow> (('a::full_exhaustive) \<Rightarrow> bool) \<Rightarrow> 'e list \<Rightarrow> bool \<Rightarrow> 's \<Rightarrow> 'e list \<Rightarrow> ('e list \<times> bool) option" where
  "cyphyaction_has_visible_trace_incremental_insts step_limit breadth unroll ts P pred [] has_tick s to_check =
    (case full_exhaustive_class.full_exhaustive
        (\<lambda> (a, term).
          if pred a then
            case cyphyaction_has_visible_trace_incremental step_limit unroll ts (P a) to_check has_tick s of
              None \<Rightarrow> Some (True, []) \<comment> \<open>the process has the trace, stop checking\<close>
            | Some _ \<Rightarrow> None \<comment> \<open>the process doesn't have the trace, continue\<close>
          else
            None)
        (natural_of_nat breadth) of
          Some _ \<Rightarrow> None \<comment> \<open>we have the trace, but we are at the end\<close>
        | None \<Rightarrow> Some (to_check, has_tick))" 
| "cyphyaction_has_visible_trace_incremental_insts step_limit breadth unroll ts P pred (e#t) has_tick s to_check =
    (case full_exhaustive_class.full_exhaustive
        (\<lambda> (a, term).
          if pred a then
            case cyphyaction_has_visible_trace_incremental step_limit unroll ts (P a) (to_check @ [e] ) has_tick s of
              None \<Rightarrow> Some (True, []) \<comment> \<open>the process has the trace, stop checking\<close>
            | Some _ \<Rightarrow> None \<comment> \<open>the process doesn't have the trace, continue\<close>
          else
            None)
        (natural_of_nat breadth) of
          Some _ \<Rightarrow> \<comment> \<open>we have the trace, try the next event\<close>
            cyphyaction_has_visible_trace_incremental_insts step_limit breadth unroll ts P pred t has_tick s (to_check @ [e] )
        | None \<Rightarrow> Some (to_check, False))"

fun cyphyaction_has_visible_trace_incremental_insts'
      :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> (('a::full_exhaustive) \<Rightarrow> ('e, 's) cyphyaction) \<Rightarrow> (('a::full_exhaustive) \<Rightarrow> bool) \<Rightarrow> 'e list \<Rightarrow> bool \<Rightarrow> 's \<Rightarrow> 'e list \<Rightarrow> ('e list \<times> bool) option" where
  "cyphyaction_has_visible_trace_incremental_insts' step_limit breadth unroll ts P pred t has_tick s to_check =
    cyphyaction_has_visible_trace_incremental_insts step_limit breadth unroll ts (cyphyaction_to_cyphyast o P) pred t has_tick s to_check"

fun full_exhaustive_opt :: "(('a :: full_exhaustive) \<times> (unit \<Rightarrow> term) \<Rightarrow> (\<bool> \<times> term list) option option) \<Rightarrow> natural \<Rightarrow> (\<bool> \<times> term list) option option" where
  "full_exhaustive_opt f n =
    (case full_exhaustive_class.full_exhaustive (case_option (Some (False, [])) id o f) n of
        Some (False, []) \<Rightarrow> None
      | r \<Rightarrow> Some r)"

find_consts "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
value "prefix [1::nat] [1, 2]"

fun cyphyaction_has_visible_trace_inferred_incremental_insts
      :: "nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> (('a::full_exhaustive) \<Rightarrow> ('e, 's) cyphyast) \<Rightarrow> 'e list \<Rightarrow> bool \<Rightarrow> 's \<Rightarrow> ('e list \<times> bool) option \<Rightarrow> 'a list \<Rightarrow> ('e list \<times> bool) option option" where
  "cyphyaction_has_visible_trace_inferred_incremental_insts step_limit unroll ts P t has_tick s ret [] = Some ret"  
| "cyphyaction_has_visible_trace_inferred_incremental_insts step_limit unroll ts P t has_tick s ret (inst#insts) =
    (case cyphyaction_has_visible_trace_inferred_incremental step_limit unroll ts (P inst) t has_tick s of
        None \<Rightarrow> None \<comment> \<open>can't determine hidden events with certainty, fail out\<close>
      | Some None \<Rightarrow> Some None \<comment> \<open>the process has the trace, stop checking\<close>
      | Some (Some (pref, b)) \<Rightarrow> \<comment> \<open>the process doesn't have the trace, continue\<close>
          cyphyaction_has_visible_trace_inferred_incremental_insts step_limit unroll ts P t has_tick s
            (case ret of
                Some (pref2, _) \<Rightarrow> if prefix pref pref2 then Some (pref, b) else ret
              | None \<Rightarrow> Some (pref, b))
            insts)" 

ML HOLogic.mk_nat

fun cyphyaction_has_visible_trace_inferred_incremental_insts'
      :: "nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> (('a::full_exhaustive) \<Rightarrow> (('e::term_of), 's) cyphyaction) \<Rightarrow> 'e list \<Rightarrow> bool \<Rightarrow> 's \<Rightarrow> 'a list \<Rightarrow> ('e list \<times> bool) option option" where
  "cyphyaction_has_visible_trace_inferred_incremental_insts' step_limit unroll ts P t has_tick s insts =
    cyphyaction_has_visible_trace_inferred_incremental_insts step_limit unroll ts (cyphyaction_to_cyphyast o P) t has_tick s None insts"

definition check_next_full_exhaustive :: "('a :: full_exhaustive) list \<Rightarrow> natural \<Rightarrow> term option" where
  "check_next_full_exhaustive xs n =
    map_option
      (hd o snd)
      (full_exhaustive_class.full_exhaustive
        (\<lambda>(x, t). if List.member xs x then None else Some (True, [t ()] ))
        n)"
definition check_next_filtered_full_exhaustive :: "('a :: full_exhaustive) list \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> natural \<Rightarrow> term option" where
  "check_next_filtered_full_exhaustive xs pred n =
    (case (full_exhaustive_class.full_exhaustive
        (\<lambda>(x, t). if List.member xs x then None else if pred x then Some (True, [t ()] ) else None)
        n) of
        Some (b, [t] ) \<Rightarrow> Some t
      | _ \<Rightarrow> None)"

ML \<open>structure Term_Option_Evaluation = Proof_Data
(
  type T = unit -> term option
  val empty: T = fn () => raise Fail "Term_Option_Evaluation"
  fun init _ = empty
);
val term_opt_cookie = (Term_Option_Evaluation.get, Term_Option_Evaluation.put, "Term_Option_Evaluation.put");\<close>

ML \<open>fun get_filtered_full_exhaustive_terms' ctxt n typ pred ts terms_left =
      if terms_left <= 0 then
              ts
            else
              let val funT = HOLogic.listT typ --> (typ --> HOLogic.boolT) --> HOLogic.code_naturalT --> @{typ "term option"}
                  val fun_term = Const (@{const_name check_next_filtered_full_exhaustive}, funT)
                  val eval_term = fun_term $ (HOLogic.mk_list typ ts) $ pred $ (HOLogic.mk_number HOLogic.code_naturalT n)
              in
                case Code_Runtime.dynamic_value_strict term_opt_cookie ctxt NONE Option.map eval_term [] of
                  NONE => ts
                | SOME t => get_filtered_full_exhaustive_terms' ctxt n typ pred (ts @ [t]) (terms_left-1)
              end              
      \<close>

ML \<open>fun get_filtered_full_exhaustive_terms ctxt n typ pred terms_needed =
      let fun f ts k =
            if k > n orelse length ts = terms_needed then
              ts
            else
              case get_filtered_full_exhaustive_terms' ctxt k typ pred ts terms_needed of
                (ts') => f ts' (k+1)
      in f [] 1
      end\<close>

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
      :: "nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool \<Rightarrow> ('e::full_exhaustive, 's) cyphyast \<Rightarrow> ('e, 's) cyphyast \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (bool \<times> term list) option" where
  "cyphycircus_trace_incremental_ref_by_no_hiding step_limit unroll ts s1 s2 has_tick P Q breadth (n::nat) =
    (if n = 0 then
      None
    else
      \<comment> \<open>try a visible event on both sides\<close>
      (full_exhaustive_class.full_exhaustive 
        (\<lambda> (e,term).
          (case (cyphyaction_check_trace step_limit unroll ts has_tick  (s1, [Visible e], Some P),
                cyphyaction_check_trace step_limit unroll ts has_tick (s2, [Visible e], Some Q)) of
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
                        (case cyphycircus_trace_incremental_ref_by_no_hiding step_limit unroll ts s1' s2' has_tick P' Q' breadth (n-1) of 
                          Some (success, term_trace) => Some (success, term () # term_trace)
                        | _ \<Rightarrow> None))
                    (x#xs) (y#ys)
            | _ \<Rightarrow> None))
                 (natural_of_nat breadth)))
          "

definition cyphycircus_trace_incremental_ref_by_no_hiding'
      :: "nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool \<Rightarrow> ('e::full_exhaustive, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (bool \<times> term list) option" where
  "cyphycircus_trace_incremental_ref_by_no_hiding' step_limit unroll ts s1 s2 has_tick P Q breadth (n::nat) =
    cyphycircus_trace_incremental_ref_by_no_hiding step_limit unroll ts s1 s2 has_tick (cyphyaction_to_cyphyast P) (cyphyaction_to_cyphyast Q) breadth n"

fun cyphycircus_trace_incremental_ref_by_inferred
      :: "nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool \<Rightarrow> ('e::full_exhaustive, 's) cyphyast \<Rightarrow> ('e, 's) cyphyast \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (bool \<times> term list) option option" where
  "cyphycircus_trace_incremental_ref_by_inferred step_limit unroll ts s1 s2 has_tick P Q breadth (n::nat) =
    (if n = 0 then
      Some None
    else
      \<comment> \<open>try a visible event on both sides\<close>
      (full_exhaustive_opt 
        (\<lambda> (e,term).
          (case (cyphyaction_check_visible_trace_inferred step_limit unroll ts has_tick [e] (s1, Some P),
                cyphyaction_check_visible_trace_inferred step_limit unroll ts has_tick [e] (s2, Some Q)) of
              (Some (Some []), Some (Some [])) \<Rightarrow> \<comment> \<open>both failed, can't get a counterexample from this\<close>
                Some None
            | (Some (Some []), Some (Some (y#ys))) \<Rightarrow> \<comment> \<open>counterexample found\<close>
                Some (Some (False, [term ()] ))
            | (Some (Some (x#xs)), Some (Some [])) \<Rightarrow> \<comment> \<open>Q failed but P succeeded, this is allowed so no counterexample\<close>
                Some None
            | (Some (Some (x#xs)), Some (Some (y#ys))) \<Rightarrow> \<comment> \<open>try all the combinations of continuations to see if we can find a counterexample\<close>
                try_product 
                  (\<lambda> p q. case (p, q) of
                    ((s1', Some P'), (s2', Some Q')) \<Rightarrow> \<comment> \<open>continue to see if there is a trace P might fail on\<close>
                        (case cyphycircus_trace_incremental_ref_by_inferred step_limit unroll ts s1' s2' has_tick P' Q' breadth (n-1) of 
                            Some (Some (has_tick, term_trace)) => Some (Some (has_tick, term () # term_trace))
                          | r \<Rightarrow> r))
                    (x#xs) (y#ys)
            | (Some _, Some _) \<Rightarrow> Some None
            | _ \<Rightarrow> None \<comment> \<open>can't determine hidden events\<close>))
                 (natural_of_nat breadth)))
          "

definition cyphycircus_trace_incremental_ref_by_inferred'
      :: "nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool \<Rightarrow> ('e::full_exhaustive, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (bool \<times> term list) option option" where
  "cyphycircus_trace_incremental_ref_by_inferred' step_limit unroll ts s1 s2 has_tick P Q breadth (n::nat) =
    cyphycircus_trace_incremental_ref_by_inferred step_limit unroll ts s1 s2 has_tick (cyphyaction_to_cyphyast P) (cyphyaction_to_cyphyast Q) breadth n"

section \<open>Running checks from ML\<close>

subsection \<open>Checking prisms are compatible with our approach to checking hiding\<close>

ML \<open>
structure String_List_Evaluation = Proof_Data
(
  type T = unit -> string list
  val empty: T = fn () => raise Fail "String_List_Evaluation"
  fun init _ = empty
);
val string_list_eval_cookie = (String_List_Evaluation.get, String_List_Evaluation.put, "String_List_Evaluation.put");
\<close>

definition chan_names :: "('a :: chantyperep) itself \<Rightarrow> String.literal list" where
  "chan_names typ =  map (chan_name) (chantyperep typ)"

ML \<open>fun chan_names ctxt typ =
      let val chan_names_term = Const (@{const_name chan_names}, Term.itselfT typ --> HOLogic.listT HOLogic.literalT) $ (Logic.mk_type typ)
          val raw_chan_names = Code_Runtime.dynamic_value_strict string_list_eval_cookie ctxt NONE (fn f => map (HOLogic.dest_string o f o HOLogic.mk_string)) chan_names_term []
          val consts = (#constants o Consts.dest o Proof_Context.consts_of) ctxt
          fun const_is_prism (_, (Type (@{type_name prism_ext}, [_, srcT, _]), _)) = (srcT = typ)
            | const_is_prism _ = false
          val prism_consts = filter const_is_prism consts
          fun is_chan_name (name, _) = member (=) raw_chan_names (Long_Name.base_name name)
          val chan_consts = filter is_chan_name prism_consts
      in map fst chan_consts
      end\<close>
ML \<open>fun is_allowed_prism ctxt term =
      case (SOME (fastype_of term) handle TERM _ => NONE) of
        SOME (Type (@{type_name prism_ext}, [_, srcT, _])) =>
          (* we are looking at a prism, check how it is constructed *)
          (case term of
            (Const (@{const_name chinst1}, _)) $ subprism $ _ => is_allowed_prism ctxt subprism
          | (Const (@{const_name chinstn}, _)) $ subprism $ _ => is_allowed_prism ctxt subprism
          | Const (prism, _) => Library.member (=) (chan_names ctxt srcT) prism
          | _ => false)
      | _ => true (* if the term isn't a prism, it doesn't matter how it is constructed *)\<close>

ML \<open>fun contains_forbidden_prism ctxt = Term.exists_subterm (not o is_allowed_prism ctxt)\<close>
ML \<open>fun contains_hiding_name t = Term.exists_Const (fn (c, _) => c = @{const_name cHide}) t\<close>

subsection \<open>\<close>

ML \<open>
structure Trace_Evaluation = Proof_Data
(
  type T = unit -> term list option
  val empty: T = fn () => raise Fail "Trace_Evaluation"
  fun init _ = empty
);
val trace_eval_cookie = (Trace_Evaluation.get, Trace_Evaluation.put, "Trace_Evaluation.put");
\<close>

ML \<open>
structure Trace_Evaluation_Opt = Proof_Data
(
  type T = unit -> term list option option
  val empty: T = fn () => raise Fail "Trace_Evaluation"
  fun init _ = empty
);
val trace_eval_opt_cookie = (Trace_Evaluation_Opt.get, Trace_Evaluation_Opt.put, "Trace_Evaluation_Opt.put");
\<close>

definition [code]: "code_real_of_rat n k \<equiv> Scaled ((n*1000000000) div k)"
definition [code]: "code_real_inv k \<equiv> code_real_of_rat 1 k"
definition [code]: "unpack_trace_check_result \<equiv> map_option (map_option (map term_of_class.term_of o fst))"

ML \<open>fun check_cyphycircus_trace_incremental_ref_by_no_hiding ctxt stT evT breadth depth step_limit unroll timestep_term has_tick spec impl = 
  let val ctxt = ensure_monomorphisations_exist ctxt spec
      val ctxt = ensure_monomorphisations_exist ctxt impl
      val actT = Type (@{type_name cyphyaction}, [evT, stT])
      val resT = @{typ "(bool \<times> term list) option"}
      val cyphycircus_trace_incremental_ref_by = Const (@{const_name cyphycircus_trace_incremental_ref_by_no_hiding'},
                HOLogic.natT --> HOLogic.natT --> HOLogic.realT --> stT --> stT --> HOLogic.boolT
                  --> actT --> actT --> HOLogic.natT --> HOLogic.natT --> resT)
      val unpack_result = @{term "map_option snd :: (bool \<times> term list) option \<Rightarrow> term list option"}
      val term = cyphycircus_trace_incremental_ref_by
                  $ (HOLogic.mk_nat step_limit)
                  $ (HOLogic.mk_nat unroll)
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

ML \<open>fun check_cyphycircus_trace_incremental_ref_by_inferred ctxt stT evT breadth depth step_limit unroll timestep_term has_tick spec impl =
  let val ctxt = ensure_monomorphisations_exist ctxt spec
      val ctxt = ensure_monomorphisations_exist ctxt impl
      val actT = Type (@{type_name cyphyaction}, [evT, stT])
      val resT = @{typ "(bool \<times> term list) option option"}
      val cyphycircus_trace_incremental_ref_by = Const (@{const_name cyphycircus_trace_incremental_ref_by_inferred'},
                HOLogic.natT --> HOLogic.natT --> HOLogic.realT --> stT --> stT --> HOLogic.boolT
                  --> actT --> actT --> HOLogic.natT --> HOLogic.natT --> resT)
      val unpack_result = @{term "map_option (map_option snd) :: (bool \<times> term list) option option \<Rightarrow> term list option option"}
      val term = cyphycircus_trace_incremental_ref_by
                  $ (HOLogic.mk_nat step_limit)
                  $ (HOLogic.mk_nat unroll)
                  $ timestep_term
                  $ (Const (@{const_name default}, stT)) (* initial state for P *)
                  $ (Const (@{const_name default}, stT)) (* initial state for Q *)
                  $ (if has_tick then @{term True} else @{term False})
                  $ spec
                  $ impl
                  $ (HOLogic.mk_nat breadth)
                  $ (HOLogic.mk_nat depth)
  in
    if contains_forbidden_prism ctxt spec orelse contains_forbidden_prism ctxt impl then
      Exn.Exn (TERM ("Specification or implementation uses channels whose events can't be statically determined", 
        [Const (@{const_name HOL.eq}, dummyT) $ Free ("specification", dummyT) $ spec, 
         Const (@{const_name HOL.eq}, dummyT) $ Free ("implementation", dummyT) $ impl]))
    else
      case Code_Runtime.dynamic_value_exn trace_eval_opt_cookie ctxt NONE (Option.map o Option.map o map) (unpack_result $ term) [] of
          Exn.Exn e => Exn.Exn e
        | Exn.Res NONE => Exn.Exn (TERM ("Specification or implementation has hidden communications with indeterminate values", 
            [Const (@{const_name HOL.eq}, dummyT) $ Free ("specification", dummyT) $ spec, 
             Const (@{const_name HOL.eq}, dummyT) $ Free ("implementation", dummyT) $ impl]))
        | Exn.Res (SOME r) => Exn.Res r
  end\<close>

ML \<open>fun check_cyphycircus_has_trace_incremental_insts ctxt stT evT breadth step_limit unroll timestep_term trace has_tick P P_pred = 
  let val ctxt = ensure_monomorphisations_exist ctxt P
      val specT = fastype_of P
      val predT = fastype_of P_pred
      val resT = @{typ "(bool \<times> term list) option"}
      val cyphycircus_has_trace_incremental = Const (@{const_name cyphyaction_has_visible_trace_incremental_insts'},
                HOLogic.natT --> HOLogic.natT --> HOLogic.natT --> HOLogic.realT --> specT --> predT --> (HOLogic.listT evT) --> HOLogic.boolT --> stT
                  --> (HOLogic.listT evT) --> resT)
      val unpack_result =  Const (@{const_name unpack_trace_check_result}, resT --> Type (@{type_name option}, [HOLogic.listT HOLogic.termT]))
      val term = cyphycircus_has_trace_incremental
                  $ (HOLogic.mk_nat step_limit)
                  $ (HOLogic.mk_nat breadth)
                  $ (HOLogic.mk_nat unroll)
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

ML \<open>fun check_cyphycircus_has_trace_incremental_inferred_insts ctxt stT evT breadth step_limit unroll timestep_term trace has_tick P P_pred = 
  let val ctxt = ensure_monomorphisations_exist ctxt P
      val specT = fastype_of P
      val predT = fastype_of P_pred
      val type_error = TYPE ("Specification and predicate must be (single-argument) functions with the same input type",[specT, predT],[P, P_pred])
      val paramT =
        case dest_Type specT of
            (@{type_name "fun"}, [inp, _]) => inp
          | _ => raise type_error
      val _ = 
        case dest_Type predT of
            (@{type_name "fun"}, [inp, _]) => if inp = paramT then () else raise type_error
          | _ => raise type_error
      val resT = Type (@{type_name option}, [Type (@{type_name option}, [HOLogic.mk_prodT (HOLogic.listT evT, @{typ bool})])])
      val insts = get_filtered_full_exhaustive_terms ctxt breadth paramT P_pred breadth
      val cyphycircus_has_trace_incremental = Const (@{const_name cyphyaction_has_visible_trace_inferred_incremental_insts'},
                HOLogic.natT --> HOLogic.natT --> HOLogic.realT --> specT --> (HOLogic.listT evT) --> HOLogic.boolT --> stT
                  --> (HOLogic.listT paramT) --> resT)
      val unpack_result = Const (@{const_name unpack_trace_check_result}, resT --> @{typ "term list option option"})
      val term = cyphycircus_has_trace_incremental
                  $ (HOLogic.mk_nat step_limit)
                  $ (HOLogic.mk_nat unroll)
                  $ timestep_term
                  $ P
                  $ (HOLogic.mk_list evT trace)
                  $ (if has_tick then @{term True} else @{term False})
                  $ (Const (@{const_name default}, stT)) (* initial state *)
                  $ (HOLogic.mk_list paramT insts)
  in if contains_forbidden_prism ctxt P then
      Exn.Exn (TERM ("Specification uses channels whose events can't be statically determined", 
        [Const (@{const_name HOL.eq}, dummyT) $ Free ("specification", dummyT) $ P]))
    else
      case Code_Runtime.dynamic_value_exn trace_eval_opt_cookie ctxt NONE (Option.map o Option.map o map) (unpack_result $ term) [] of
          Exn.Exn e => Exn.Exn e
        | Exn.Res NONE => Exn.Exn (TERM ("Specification has hidden communications with indeterminate values", 
            [Const (@{const_name HOL.eq}, dummyT) $ Free ("specification", dummyT) $ P]))
        | Exn.Res (SOME r) => Exn.Res r
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

ML \<open>fun repeat _ 0 = []
      | repeat x n = x :: repeat x (n-1)\<close>

ML \<open>fun add_timings {elapsed=elapsed1, cpu=cpu1, gc=gc1}
                    {elapsed=elapsed2: Time.time, cpu=cpu2: Time.time, gc=gc2: Time.time}
      = {elapsed = elapsed1+elapsed2, cpu = cpu1+cpu2, gc = gc1+gc2}\<close>
ML \<open>fun scale_timing x {elapsed: Time.time, cpu: Time.time, gc: Time.time}
      = {elapsed=Time.scale x elapsed, cpu = Time.scale x cpu, gc = Time.scale x gc}\<close>
ML \<open>fun profile_times n x f =
          let val timings = map (fst o Timing.timing f) (repeat x n)
              val avg_timing = scale_timing (1.0 / Real.fromInt n) (fold add_timings timings Timing.zero)
          in writeln ("Average Times: " ^ Timing.message avg_timing)
          end\<close>

abbreviation "test_events \<equiv> [b_C (), a_C 0, a_C 1, a_C 2, a_C 3, a_C 4]"
abbreviation "test_traces \<equiv> b_lists 4 test_events"
abbreviation "visibility_test_events \<equiv> map Visible test_events @ map (Hidden 0) test_events @ map (Hidden 1) test_events"
abbreviation "test_visibility_traces \<equiv> b_lists 4 visibility_test_events"
abbreviation "traces_of P \<equiv>
  map (\<lambda>t. (t, False))
    (filter (\<lambda>t. Option.is_none (cyphyaction_has_visible_trace_incremental' 1000 10 (code_real_inv 100) P t False (default::bar))) test_traces)
  @ map (\<lambda>t. (t, True))
    (filter (\<lambda>t. Option.is_none (cyphyaction_has_visible_trace_incremental' 1000 10 (code_real_inv 100) P t True (default::bar))) test_traces)"
abbreviation "check_inferred_trace P has_tick t \<equiv>
  case cyphyaction_has_visible_trace_inferred_incremental' 1000 10 (code_real_inv 100) P t has_tick (default::bar) of
      None \<Rightarrow> Some None
    | Some None \<Rightarrow> Some (Some t)
    | Some (Some r) \<Rightarrow> None"
abbreviation "inferred_traces_of P \<equiv>
  combine_options (@)
    (map_option (map (\<lambda>t. (t, False))) (those (List.map_filter (check_inferred_trace P False) test_traces)))
    (map_option (map (\<lambda>t. (t, True))) (those (List.map_filter (check_inferred_trace P True) test_traces)))"
abbreviation "visibility_traces_of P \<equiv>
  map (\<lambda>t. (t, False))
    (filter (\<lambda>t. Option.is_none (cyphyaction_has_trace_incremental' 1000 10 (code_real_inv 100) P t False (default::bar))) test_visibility_traces)
  @ map (\<lambda>t. (t, True))
    (filter (\<lambda>t. Option.is_none (cyphyaction_has_trace_incremental' 1000 10 (code_real_inv 100) P t True (default::bar))) test_visibility_traces)"

subsection \<open>Test 1: @{term "a\<^bold>.1 \<rightarrow> a\<^bold>!2 \<rightarrow> Skip \<sqsubseteq> a\<^bold>.1 \<rightarrow> a\<^bold>!0 \<rightarrow> Skip"} gives @{term "[a_C 1, a_C 0]"}\<close>

ML \<open>let val term_string = Pretty.pure_string_of o Syntax.pretty_term @{context}
        fun traceToString trace = String.concatWith " \<rightarrow> " (map term_string trace)
    in timeit 
      (fn () => Option.map traceToString (Exn.release (check_cyphycircus_trace_incremental_ref_by_no_hiding @{context} @{typ bar} @{typ foo} 10 10 1000 1 @{term "code_real_inv 100"} false
      @{term "a\<^bold>.1 \<rightarrow> a\<^bold>!2 \<rightarrow> Skip :: (foo, bar) cyphyaction"}
      @{term "a\<^bold>.1 \<rightarrow> a\<^bold>!0 \<rightarrow> Skip :: (foo, bar) cyphyaction"})))
    end\<close>

value "traces_of (a\<^bold>.1 \<rightarrow> a\<^bold>!2 \<rightarrow> Skip)"
value "traces_of (a\<^bold>.1 \<rightarrow> a\<^bold>!0 \<rightarrow> Skip)"

ML \<open>let val term_string = Pretty.pure_string_of o Syntax.pretty_term @{context}
        fun traceToString trace = String.concatWith " \<rightarrow> " (map term_string trace)
    in timeit
      (fn () => Option.map traceToString (Exn.release (check_cyphycircus_trace_incremental_ref_by_inferred @{context} @{typ bar} @{typ foo} 10 10 1000 1 @{term "code_real_inv 100"} false
      @{term "a\<^bold>.1 \<rightarrow> a\<^bold>!2 \<rightarrow> Skip :: (foo, bar) cyphyaction"}
      @{term "a\<^bold>.1 \<rightarrow> a\<^bold>!0 \<rightarrow> Skip :: (foo, bar) cyphyaction"})))
    end\<close>

value "inferred_traces_of (a\<^bold>.1 \<rightarrow> a\<^bold>!2 \<rightarrow> Skip)"
value "inferred_traces_of (a\<^bold>.1 \<rightarrow> a\<^bold>!0 \<rightarrow> Skip)"

subsection \<open>Test 2: @{term "a\<^bold>.1 \<rightarrow> a\<^bold>!0 \<rightarrow>  Skip \<sqsubseteq> a\<^bold>.1 \<rightarrow> a\<^bold>?x \<rightarrow> Skip"} gives @{term "[a_C 1, a_C 1]"}\<close>

ML \<open>let val term_string = Pretty.pure_string_of o Syntax.pretty_term @{context}
        fun traceToString trace = String.concatWith " \<rightarrow> " (map term_string trace)
    in timeit 
      (fn () => Option.map traceToString (Exn.release (check_cyphycircus_trace_incremental_ref_by_no_hiding @{context} @{typ bar} @{typ foo} 10 10 1000 1 @{term "code_real_inv 100"} false
      @{term "a\<^bold>.1 \<rightarrow> a\<^bold>!0 \<rightarrow> Skip :: (foo, bar) cyphyaction"}
      @{term "a\<^bold>.1 \<rightarrow> a\<^bold>?x \<rightarrow> Skip :: (foo, bar) cyphyaction"})))
    end\<close>

value "traces_of (a\<^bold>.1 \<rightarrow> a\<^bold>!0 \<rightarrow> Skip)"
value "traces_of (a\<^bold>.1 \<rightarrow> a\<^bold>?x \<rightarrow> Skip)"

ML \<open>let val term_string = Pretty.pure_string_of o Syntax.pretty_term @{context}
        fun traceToString trace = String.concatWith " \<rightarrow> " (map term_string trace)
    in timeit 
      (fn () => Option.map traceToString (Exn.release (check_cyphycircus_trace_incremental_ref_by_inferred @{context} @{typ bar} @{typ foo} 10 10 1000 1 @{term "code_real_inv 100"} false
      @{term "a\<^bold>.1 \<rightarrow> a\<^bold>!0 \<rightarrow> Skip :: (foo, bar) cyphyaction"}
      @{term "a\<^bold>.1 \<rightarrow> a\<^bold>?x \<rightarrow> Skip :: (foo, bar) cyphyaction"})))
    end\<close>

value "inferred_traces_of (a\<^bold>.1 \<rightarrow> a\<^bold>!0 \<rightarrow> Skip)"
value "inferred_traces_of (a\<^bold>.1 \<rightarrow> a\<^bold>?x \<rightarrow> Skip)"

subsection \<open>Test 3: @{term "b \<rightarrow> Skip \<sqsubseteq> (\<mu> X. b \<rightarrow> X)"} gives @{term "[b_C (), b_C ()]"}\<close>

recursive where "baz = b \<rightarrow> baz"

ML \<open>let val term_string = Pretty.pure_string_of o Syntax.pretty_term @{context}
        fun traceToString trace = String.concatWith " \<rightarrow> " (map term_string trace)
    in timeit
      (fn () => Option.map traceToString (Exn.release (check_cyphycircus_trace_incremental_ref_by_no_hiding @{context} @{typ bar} @{typ foo} 10 10 1000 2 @{term "code_real_inv 100"} false
       @{term "b \<rightarrow> Skip :: (foo, bar) cyphyaction"}
      (Raw_Simplifier.rewrite_term @{theory} @{thms recursive_defs rec_sys_defs cyphyaction_datatype_unfolds} [] @{term "baz :: (foo, bar) cyphyaction"}))))
    end\<close>

value "traces_of (b \<rightarrow> Skip)"
value "traces_of (baz)"

ML \<open>let val term_string = Pretty.pure_string_of o Syntax.pretty_term @{context}
        fun traceToString trace = String.concatWith " \<rightarrow> " (map term_string trace)
    in timeit
      (fn () => Option.map traceToString (Exn.release (check_cyphycircus_trace_incremental_ref_by_inferred @{context} @{typ bar} @{typ foo} 10 10 1000 2 @{term "code_real_inv 100"} false
      @{term "b \<rightarrow> Skip :: (foo, bar) cyphyaction"}
      (Raw_Simplifier.rewrite_term @{theory} @{thms recursive_defs rec_sys_defs cyphyaction_datatype_unfolds} [] @{term "baz :: (foo, bar) cyphyaction"}))))
    end\<close>

value "inferred_traces_of (b \<rightarrow> Skip)"
value "inferred_traces_of (baz)"

subsection \<open>Test 4: @{term "(\<mu> X. b \<rightarrow> X) \<sqsubseteq> b \<rightarrow> Skip"} gives @{term "[b_C ()]"} with tick}\<close>

ML \<open>let val term_string = Pretty.pure_string_of o Syntax.pretty_term @{context}
        fun traceToString trace = String.concatWith " \<rightarrow> " (map term_string trace)
    in timeit
      (fn () => Option.map traceToString (Exn.release (check_cyphycircus_trace_incremental_ref_by_no_hiding @{context} @{typ bar} @{typ foo} 10 10 1000 2 @{term "code_real_inv 100"} true
      (Raw_Simplifier.rewrite_term @{theory} @{thms recursive_defs rec_sys_defs cyphyaction_datatype_unfolds} [] @{term "baz :: (foo, bar) cyphyaction"})
      @{term "b \<rightarrow> Skip :: (foo, bar) cyphyaction"})))
    end\<close>

ML \<open>let val term_string = Pretty.pure_string_of o Syntax.pretty_term @{context}
        fun traceToString trace = String.concatWith " \<rightarrow> " (map term_string trace)
    in timeit
      (fn () => Option.map traceToString (Exn.release (check_cyphycircus_trace_incremental_ref_by_inferred @{context} @{typ bar} @{typ foo} 10 10 1000 2 @{term "code_real_inv 100"} true
      (Raw_Simplifier.rewrite_term @{theory} @{thms recursive_defs rec_sys_defs cyphyaction_datatype_unfolds} [] @{term "baz :: (foo, bar) cyphyaction"})
      @{term "b \<rightarrow> Skip :: (foo, bar) cyphyaction"})))
    end\<close>

subsection \<open>Test 5: Continuous Evolution test, expect trace @{term "[a_C 2, a_C 4, a_C 6]"} etc.}\<close>

recursive where
  "test5_cont =
    (cEvolve (v +\<^sub>L time) (\<lambda>_. \<lparr>n\<^sub>v=0, v\<^sub>v=2, time\<^sub>v=1\<rparr>) (time < 1)\<^sub>e) ;; time := 0 ;;
    a\<^bold>!(nat (floor v)) \<rightarrow> test5_cont"
recursive where
  "test5_discr = n := n+2 ;; a\<^bold>!n \<rightarrow> test5_discr"

ML \<open>Term.exists_subterm (fn t => case t of Const (@{const_name cEvolve},_) => true | _ => false)\<close>
ML \<open>val unfolded_term = unfold_cyphyaction_defs @{context} @{term "test5_cont :: (foo, bar) cyphyaction"};
    collect_CEvolve_types unfolded_term\<close>
local_setup \<open>fn ctxt => ensure_monomorphisations_exist @{context} @{term "test5_cont :: (foo, bar) cyphyaction"}\<close>
print_theorems
text \<open>Refinement @{term "test5_cont \<sqsubseteq> a\<^bold>!2 \<rightarrow> a\<^bold>!0 \<rightarrow>  Skip"}, gives @{term "[a_C 2, a_C 0]"}\<close>
ML \<open>let val term_string = Pretty.pure_string_of o Syntax.pretty_term @{context}
        fun traceToString trace = String.concatWith " \<rightarrow> " (map term_string trace)
    in timeit
      (fn () => Option.map traceToString (Exn.release (check_cyphycircus_trace_incremental_ref_by_no_hiding @{context} @{typ bar} @{typ foo} 10 10 1000 2 @{term "code_real_inv 100"} false
      (@{term "test5_cont :: (foo, bar) cyphyaction"})
      @{term "a\<^bold>!2 \<rightarrow> a\<^bold>!0 \<rightarrow>  Skip :: (foo, bar) cyphyaction"})))
    end\<close>

ML \<open>let val term_string = Pretty.pure_string_of o Syntax.pretty_term @{context}
        fun traceToString trace = String.concatWith " \<rightarrow> " (map term_string trace)
    in timeit
      (fn () => Option.map traceToString (Exn.release (check_cyphycircus_trace_incremental_ref_by_no_hiding @{context} @{typ bar} @{typ foo} 10 10 1000 2 @{term "code_real_inv 100"} false
      (@{term "test5_cont :: (foo, bar) cyphyaction"})
      @{term "test5_discr :: (foo, bar) cyphyaction"})))
    end\<close>

value "traces_of test5_cont"
value "traces_of test5_discr"
value "cyphyaction_has_visible_trace_incremental' 1000 10 (code_real_inv 100) test5_cont [a_C 2, a_C 4, a_C 6, a_C 8, a_C 10] False (default::bar)"
value "cyphyaction_has_visible_trace_incremental' 1000 10 (code_real_inv 100) test5_cont [a_C 2, a_C 4, a_C 6, a_C 8, a_C 10] True (default::bar)"
value "cyphyaction_has_visible_trace_incremental' 1000 10 (code_real_inv 100) test5_cont [a_C 2, a_C 4, a_C 6, a_C 8, a_C 0] False (default::bar)"

text \<open>Refinement @{term "test5_cont \<sqsubseteq> a\<^bold>!2 \<rightarrow> a\<^bold>!0 \<rightarrow>  Skip"}, gives @{term "[a_C 2, a_C 0]"}\<close>
ML \<open>let val term_string = Pretty.pure_string_of o Syntax.pretty_term @{context}
        fun traceToString trace = String.concatWith " \<rightarrow> " (map term_string trace)
    in timeit
      (fn () => Option.map traceToString (Exn.release (check_cyphycircus_trace_incremental_ref_by_inferred @{context} @{typ bar} @{typ foo} 10 10 1000 2 @{term "code_real_inv 100"} false
      (@{term "test5_cont :: (foo, bar) cyphyaction"})
      @{term "a\<^bold>!2 \<rightarrow> a\<^bold>!0 \<rightarrow>  Skip :: (foo, bar) cyphyaction"})))
    end\<close>

ML \<open>let val term_string = Pretty.pure_string_of o Syntax.pretty_term @{context}
        fun traceToString trace = String.concatWith " \<rightarrow> " (map term_string trace)
    in timeit
      (fn () => Option.map traceToString (Exn.release (check_cyphycircus_trace_incremental_ref_by_inferred @{context} @{typ bar} @{typ foo} 10 10 1000 2 @{term "code_real_inv 100"} false
      (@{term "test5_cont :: (foo, bar) cyphyaction"})
      @{term "test5_discr :: (foo, bar) cyphyaction"})))
    end\<close>

value "inferred_traces_of test5_cont"
value "inferred_traces_of test5_discr"
value "cyphyaction_has_visible_trace_inferred_incremental' 1000 10 (code_real_inv 100) test5_cont [a_C 2, a_C 4, a_C 6, a_C 8, a_C 10] False (default::bar)"
value "cyphyaction_has_visible_trace_inferred_incremental' 1000 10 (code_real_inv 100) test5_cont [a_C 2, a_C 4, a_C 6, a_C 8, a_C 10] True (default::bar)"
value "cyphyaction_has_visible_trace_inferred_incremental' 1000 10 (code_real_inv 100) test5_cont [a_C 2, a_C 4, a_C 6, a_C 8, a_C 0] False (default::bar)"


subsection \<open>Test 6: Parallelism and hiding test\<close>

text \<open>Refinement @{term "((a\<^bold>.0 \<rightarrow> b \<rightarrow> Skip) \<lbrakk>\<^bold>0|\<lbrace>b\<rbrace>|\<^bold>0\<rbrakk> (b \<rightarrow> a\<^bold>.1 \<rightarrow> Skip)) \<Zhide> \<lbrace>b\<rbrace> \<sqsubseteq> a\<^bold>!0 \<rightarrow> b \<rightarrow> a\<^bold>!1 \<rightarrow>  Skip"}
      gives @{term "[a_C 0, b_C ()]"}. This ensures hidden events are, in fact, hidden.\<close>

text \<open>errors out on refinement check due to hiding\<close>
ML \<open>case (check_cyphycircus_trace_incremental_ref_by_no_hiding @{context} @{typ bar} @{typ foo} 10 10 1000 1 @{term "code_real_inv 100"} false
      (@{term "((a\<^bold>.0 \<rightarrow> b \<rightarrow> Skip) \<lbrakk>\<^bold>0|\<lbrace>b\<rbrace>|\<^bold>0\<rbrakk> (b \<rightarrow> a\<^bold>.1 \<rightarrow> Skip)) \<Zhide> \<lbrace>b\<rbrace> :: (foo, bar) cyphyaction"})
      @{term "a\<^bold>!0 \<rightarrow> b \<rightarrow> a\<^bold>!1 \<rightarrow>  Skip :: (foo, bar) cyphyaction"}) of
        Exn.Res _ => error "Expected exception to be thrown"
      | Exn.Exn e => if Exn.is_interrupt e then Exn.reraise e else (writeln o Runtime.exn_message o (Runtime.exn_context (SOME @{context}))) e\<close> 
ML \<open>case (check_cyphycircus_trace_incremental_ref_by_no_hiding @{context} @{typ bar} @{typ foo} 10 10 1000 1 @{term "code_real_inv 100"} false
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

text \<open>successfully gives @{term "[a_C 0, b_C ()]"}\<close>
ML \<open>let val term_string = Pretty.pure_string_of o Syntax.pretty_term @{context}
        fun traceToString trace = String.concatWith " \<rightarrow> " (map term_string trace)
    in  timeit
      (fn () => Option.map traceToString (Exn.release (check_cyphycircus_trace_incremental_ref_by_inferred @{context} @{typ bar} @{typ foo} 10 10 1000 1 @{term "code_real_inv 100"} false
      @{term "((a\<^bold>.0 \<rightarrow> b \<rightarrow> Skip) \<lbrakk>\<^bold>0|\<lbrace>b\<rbrace>|\<^bold>0\<rbrakk> (b \<rightarrow> a\<^bold>.1 \<rightarrow> Skip)) \<Zhide> \<lbrace>b\<rbrace> :: (foo, bar) cyphyaction"}
      @{term "a\<^bold>!0 \<rightarrow> b \<rightarrow> a\<^bold>!1 \<rightarrow>  Skip :: (foo, bar) cyphyaction"})))
    end\<close> 

text \<open>refinement succeeds without the hidden event on one side\<close>

ML \<open>let val term_string = Pretty.pure_string_of o Syntax.pretty_term @{context}
        fun traceToString trace = String.concatWith " \<rightarrow> " (map term_string trace)
    in timeit
      (fn () => Option.map traceToString (Exn.release (check_cyphycircus_trace_incremental_ref_by_inferred @{context} @{typ bar} @{typ foo} 10 10 1000 1 @{term "code_real_inv 100"} false
      @{term "((a\<^bold>.0 \<rightarrow> b \<rightarrow> Skip) \<lbrakk>\<^bold>0|\<lbrace>b\<rbrace>|\<^bold>0\<rbrakk> (b \<rightarrow> a\<^bold>.1 \<rightarrow> Skip)) \<Zhide> \<lbrace>b\<rbrace> :: (foo, bar) cyphyaction"}
      @{term "a\<^bold>!0 \<rightarrow> a\<^bold>!1 \<rightarrow>  Skip :: (foo, bar) cyphyaction"})))
    end\<close>
ML \<open>let val term_string = Pretty.pure_string_of o Syntax.pretty_term @{context}
        fun traceToString trace = String.concatWith " \<rightarrow> " (map term_string trace)
    in timeit
      (fn () => Option.map traceToString (Exn.release (check_cyphycircus_trace_incremental_ref_by_inferred @{context} @{typ bar} @{typ foo} 10 10 1000 1 @{term "code_real_inv 100"} false
      @{term "a\<^bold>!0 \<rightarrow> a\<^bold>!1 \<rightarrow>  Skip :: (foo, bar) cyphyaction"}
      @{term "((a\<^bold>.0 \<rightarrow> b \<rightarrow> Skip) \<lbrakk>\<^bold>0|\<lbrace>b\<rbrace>|\<^bold>0\<rbrakk> (b \<rightarrow> a\<^bold>.1 \<rightarrow> Skip)) \<Zhide> \<lbrace>b\<rbrace> :: (foo, bar) cyphyaction"}))) 
    end\<close>


value "inferred_traces_of (((a\<^bold>.0 \<rightarrow> b \<rightarrow> Skip) \<lbrakk>\<^bold>0|\<lbrace>b\<rbrace>|\<^bold>0\<rbrakk> (b \<rightarrow> a\<^bold>.1 \<rightarrow> Skip)) \<Zhide> \<lbrace>b\<rbrace>)"
value "inferred_traces_of (a\<^bold>!0 \<rightarrow> a\<^bold>!1 \<rightarrow>  Skip)"


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
    in timeit
      (fn () => Option.map traceToString (Exn.release (check_cyphycircus_trace_incremental_ref_by_no_hiding @{context} @{typ bar} @{typ foo} 10 10 1000 1 @{term "code_real_inv 100"} false
      (Raw_Simplifier.rewrite_term @{theory} @{thms recursive_defs rec_sys_defs cyphyaction_datatype_unfolds} [] @{term "test7 :: (foo, bar) cyphyaction"})
      @{term "a\<^bold>!0 \<rightarrow> a\<^bold>!1 \<rightarrow> b \<rightarrow>  Skip :: (foo, bar) cyphyaction"})))
    end\<close>
ML \<open>let val term_string = Pretty.pure_string_of o Syntax.pretty_term @{context}
        fun traceToString trace = String.concatWith " \<rightarrow> " (map term_string trace)
    in profile_times 20 () 
      (fn () => Option.map traceToString (Exn.release (check_cyphycircus_trace_incremental_ref_by_inferred @{context} @{typ bar} @{typ foo} 10 10 1000 1 @{term "code_real_inv 100"} false
      (Raw_Simplifier.rewrite_term @{theory} @{thms recursive_defs rec_sys_defs cyphyaction_datatype_unfolds} [] @{term "test7 :: (foo, bar) cyphyaction"})
      @{term "a\<^bold>!0 \<rightarrow> a\<^bold>!1 \<rightarrow> b \<rightarrow>  Skip :: (foo, bar) cyphyaction"})))
    end\<close>

value "traces_of test7"
value "inferred_traces_of test7"


subsection \<open>Test 8: refinement @{term "a\<^bold>!0 \<rightarrow> (inf (a\<^bold>!1 \<rightarrow>  Skip) (a\<^bold>!2 \<rightarrow>  Skip)) \<sqsubseteq> a\<^bold>!0 \<rightarrow> a\<^bold>!1 \<rightarrow>  Skip"} holds\<close>

ML \<open>let val term_string = Pretty.pure_string_of o Syntax.pretty_term @{context}
        fun traceToString trace = String.concatWith " \<rightarrow> " (map term_string trace)
    in timeit
      (fn () => Option.map traceToString (Exn.release (check_cyphycircus_trace_incremental_ref_by_no_hiding @{context} @{typ bar} @{typ foo} 10 10 1000 1 @{term "code_real_inv 100"} false
      @{term "a\<^bold>!0 \<rightarrow> (inf (a\<^bold>!1 \<rightarrow>  Skip) (a\<^bold>!2 \<rightarrow>  Skip)) :: (foo, bar) cyphyaction"}
      @{term "a\<^bold>!0 \<rightarrow> a\<^bold>!1 \<rightarrow>  Skip :: (foo, bar) cyphyaction"})))
    end\<close>
ML \<open>let val term_string = Pretty.pure_string_of o Syntax.pretty_term @{context}
        fun traceToString trace = String.concatWith " \<rightarrow> " (map term_string trace)
    in timeit
      (fn () => Option.map traceToString (Exn.release (check_cyphycircus_trace_incremental_ref_by_inferred @{context} @{typ bar} @{typ foo} 10 10 1000 1 @{term "code_real_inv 100"} false
      @{term "a\<^bold>!0 \<rightarrow> (inf (a\<^bold>!1 \<rightarrow>  Skip) (a\<^bold>!2 \<rightarrow>  Skip)) :: (foo, bar) cyphyaction"}
      @{term "a\<^bold>!0 \<rightarrow> a\<^bold>!1 \<rightarrow>  Skip :: (foo, bar) cyphyaction"})))
    end\<close>

value "traces_of (a\<^bold>!0 \<rightarrow> (inf (a\<^bold>!1 \<rightarrow>  Skip) (a\<^bold>!2 \<rightarrow>  Skip)))"
value "inferred_traces_of (a\<^bold>!0 \<rightarrow> (inf (a\<^bold>!1 \<rightarrow>  Skip) (a\<^bold>!2 \<rightarrow>  Skip)))"

subsection \<open>Test 9: refinement @{term "a\<^bold>!0 \<rightarrow> a\<^bold>!1 \<rightarrow>  Skip \<sqsubseteq> a\<^bold>!0 \<rightarrow> (inf (a\<^bold>!1 \<rightarrow>  Skip) (a\<^bold>!2 \<rightarrow>  Skip))"} gives @{term "[a_C 0, a_C 2]"}\<close>

ML \<open>let val term_string = Pretty.pure_string_of o Syntax.pretty_term @{context}
        fun traceToString trace = String.concatWith " \<rightarrow> " (map term_string trace)
    in timeit
      (fn () => Option.map traceToString (Exn.release (check_cyphycircus_trace_incremental_ref_by_no_hiding @{context} @{typ bar} @{typ foo} 10 10 1000 1 @{term "code_real_inv 100"} false
      @{term "a\<^bold>!0 \<rightarrow> a\<^bold>!1 \<rightarrow>  Skip :: (foo, bar) cyphyaction"}      
      @{term "a\<^bold>!0 \<rightarrow> (inf (a\<^bold>!1 \<rightarrow>  Skip) (a\<^bold>!2 \<rightarrow>  Skip)) :: (foo, bar) cyphyaction"})))
    end\<close>
ML \<open>let val term_string = Pretty.pure_string_of o Syntax.pretty_term @{context}
        fun traceToString trace = String.concatWith " \<rightarrow> " (map term_string trace)
    in timeit
      (fn () => Option.map traceToString (Exn.release (check_cyphycircus_trace_incremental_ref_by_inferred @{context} @{typ bar} @{typ foo} 10 10 1000 1 @{term "code_real_inv 100"} false
      @{term "a\<^bold>!0 \<rightarrow> a\<^bold>!1 \<rightarrow>  Skip :: (foo, bar) cyphyaction"}      
      @{term "a\<^bold>!0 \<rightarrow> (inf (a\<^bold>!1 \<rightarrow>  Skip) (a\<^bold>!2 \<rightarrow>  Skip)) :: (foo, bar) cyphyaction"})))
    end\<close>

hide_type foo bar

hide_const n v time a b

(*section \<open>Allowing code generation to happen ahead-of-time\<close>

code_reflect CyPhyAction_Codegen
  datatypes cyphyaction = _
    and nat
    and int = _
    and real = _
    and rat = _
    and prism_ext = _
  functions nat integer_of_nat times_nat_inst.times_nat plus_nat_inst.plus_nat minus_nat_inst.minus_nat zero_nat_inst.zero_nat one_nat_inst.one_nat
*)    


end
