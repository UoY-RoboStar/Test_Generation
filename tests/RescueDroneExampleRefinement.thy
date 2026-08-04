theory RescueDroneExampleRefinement
  imports Test_Generation.TestGen
begin

section \<open>RescueDrone Output0 refinement walkthrough\<close>

datatype InOut = In | Out

chantype rescueDrone_chans =
  tock :: unit
  moveCall :: nat
  turnBackCall :: unit
  found :: InOut
  origin :: InOut
  takeoff :: InOut
  land :: InOut

abbreviation "TOP == 1"
abbreviation "LV == 1"
abbreviation "TURN == 1"
abbreviation "DELIVERY == 2"

fun Wait :: "nat \<Rightarrow> (rescueDrone_chans, unit) cyphyaction" where
  "Wait 0 = Skip"
| "Wait (Suc n) = tock \<rightarrow> Wait n"

definition await_trigger ::
  "(rescueDrone_chans, unit) cyphyaction \<Rightarrow>
    (rescueDrone_chans, unit) cyphyaction"
where
  "await_trigger P = \<mu> (\<lambda>X. P \<box> tock \<rightarrow> X)"

definition RescueDrone :: "(rescueDrone_chans, unit) cyphyaction" where
  "RescueDrone = \<mu> (\<lambda>X.
    (takeoff\<^bold>.Out \<rightarrow> Wait TOP) ;;
    (moveCall\<^bold>.LV \<rightarrow> Skip) ;;
    await_trigger (found\<^bold>.In \<rightarrow> (land\<^bold>.Out \<rightarrow> Skip)) ;;
    Wait DELIVERY ;;
    ((takeoff\<^bold>.Out \<rightarrow> Wait TOP) ;;
      (turnBackCall \<rightarrow> Wait TURN) ;;
      (moveCall\<^bold>.LV \<rightarrow> Skip)) ;;
    await_trigger
      ((origin\<^bold>.In \<rightarrow> (turnBackCall \<rightarrow> Wait TURN)) ;;
        (land\<^bold>.Out \<rightarrow> Skip)) ;;
    X)"

definition RescueDrone_mTransTarget_Output0 ::
  "(rescueDrone_chans, unit) cyphyaction"
where
  "RescueDrone_mTransTarget_Output0 = \<mu> (\<lambda>X.
    (takeoff\<^bold>.Out \<rightarrow> Wait TOP) ;;
    Wait DELIVERY ;;
    ((takeoff\<^bold>.Out \<rightarrow> Wait TOP) ;;
      (turnBackCall \<rightarrow> Wait TURN) ;;
      (moveCall\<^bold>.LV \<rightarrow> Skip)) ;;
    await_trigger
      ((origin\<^bold>.In \<rightarrow> (turnBackCall \<rightarrow> Wait TURN)) ;;
        (land\<^bold>.Out \<rightarrow> Skip)) ;;
    X)"

subsection \<open>Refinement and counterexample walkthrough\<close>

lemma Wait_one [cyphy_model_unfolding]:
  "Wait 1 = tock \<rightarrow> Skip"
  by (simp only: One_nat_def Wait.simps)

lemma Wait_two [cyphy_model_unfolding]:
  "Wait 2 = tock \<rightarrow> tock \<rightarrow> Skip"
  by (simp only: numeral_2_eq_2 One_nat_def Wait.simps)

declare await_trigger_def [cyphy_model_unfolding]
declare RescueDrone_def [cyphy_model_unfolding]
declare RescueDrone_mTransTarget_Output0_def [cyphy_model_unfolding]

ML_val \<open>
  val specification = \<^term>\<open>RescueDrone\<close>
  val mutant = \<^term>\<open>RescueDrone_mTransTarget_Output0\<close>
  val (result, ctxt) = checkRefinement \<^context> specification mutant

  val _ =
    (case result of
      CyPhy_CheckRefinement.ProvedRefines =>
        error "Output0 unexpectedly proved refinement"
    | CyPhy_CheckRefinement.Normalised (stage as {spec, impl}) =>
        let
          val _ = writeln ("Normalised specification:\n  " ^
            Syntax.string_of_term ctxt spec)
          val _ = writeln ("Normalised mutant:\n  " ^
            Syntax.string_of_term ctxt impl)
        in
          (case obtainCounterexample ctxt stage of
            (SOME trace, _) =>
              writeln ("Quickcheck counterexample:\n  " ^
                String.concatWith " \<rightarrow> "
                  (map (Syntax.string_of_term ctxt) trace))
          | (NONE, _) =>
              error "Quickcheck found no Output0 counterexample within the configured bounds")
        end)
\<close>

end
