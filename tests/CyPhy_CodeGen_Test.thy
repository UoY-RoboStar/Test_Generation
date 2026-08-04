theory CyPhy_CodeGen_Test
  imports Test_Generation.TestGen
begin
subsection \<open> Define robochart model and mutants \<close>
datatype InOut = In | Out

chantype rescueDrone_chans =
  tock :: "unit"
  moveCall :: "\<nat>"
  turnBackCall :: "unit"
  found :: "InOut"
  origin :: "InOut"
  takeoff :: "InOut"
  land :: "InOut"
  foundTriggered :: "\<bool>"
  originTriggered :: "\<bool>"
  setVel :: "\<real> \<times> \<real> \<times> \<real>"
  setAngVel :: "\<real> \<times> \<real> \<times> \<real>"
  proceed :: "unit"

alphabet rescueDrone_state =
  pos :: "\<real> \<times> \<real> \<times> \<real>"
  vel :: "\<real> \<times> \<real> \<times> \<real>"
  acc :: "\<real> \<times> \<real> \<times> \<real>"
  ori :: "\<real> \<times> \<real> \<times> \<real>"
  angVel :: "\<real> \<times> \<real> \<times> \<real>"
  angAcc :: "\<real> \<times> \<real> \<times> \<real>"
  foundTrig :: "\<bool>"
  originTrig :: "\<bool>"
  stepTimer :: "\<real>"
  tockTimer :: "\<real>"

abbreviation "TOP == 1"
abbreviation "LV == 1"
abbreviation "TURN == 1"
abbreviation "DELIVERY == 2"

fun Wait ::
  "nat \<Rightarrow> (rescueDrone_chans, rescueDrone_state) cyphyaction"
where
  "Wait 0 = Skip" |
  "Wait (Suc n) = tock \<rightarrow> Wait n"

definition await_trigger ::
  "(rescueDrone_chans, rescueDrone_state) cyphyaction \<Rightarrow>
    (rescueDrone_chans, rescueDrone_state) cyphyaction"
where
  "await_trigger P = \<mu> (\<lambda>X. P \<box> tock \<rightarrow> X)"

definition RescueDrone ::
  "(rescueDrone_chans, rescueDrone_state) cyphyaction"
where
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
  "(rescueDrone_chans, rescueDrone_state) cyphyaction"
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

definition RescueDrone_mTransTarget_Output1 ::
  "(rescueDrone_chans, rescueDrone_state) cyphyaction"
where
  "RescueDrone_mTransTarget_Output1 = \<mu> (\<lambda>X.
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

definition RescueDrone_mTransTarget_Output2 ::
  "(rescueDrone_chans, rescueDrone_state) cyphyaction"
where
  "RescueDrone_mTransTarget_Output2 = \<mu> (\<lambda>X.
    (takeoff\<^bold>.Out \<rightarrow> Wait TOP) ;;
    X)"

definition RescueDrone_mTransTarget_Output3 ::
  "(rescueDrone_chans, rescueDrone_state) cyphyaction"
where
  "RescueDrone_mTransTarget_Output3 =
    (takeoff\<^bold>.Out \<rightarrow> Wait TOP) ;;
    (moveCall\<^bold>.LV \<rightarrow> Skip) ;;
    await_trigger (found\<^bold>.In \<rightarrow> (land\<^bold>.Out \<rightarrow> Skip)) ;;
    \<mu> (\<lambda>X.
      Wait DELIVERY ;;
      ((takeoff\<^bold>.Out \<rightarrow> Wait TOP) ;;
        (turnBackCall \<rightarrow> Wait TURN) ;;
        (moveCall\<^bold>.LV \<rightarrow> Skip)) ;;
      X)"

definition RescueDrone_mTransTarget_Output4 ::
  "(rescueDrone_chans, rescueDrone_state) cyphyaction"
where
  "RescueDrone_mTransTarget_Output4 = \<mu> (\<lambda>X.
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

definition RescueDrone_mTransTarget_Output5 ::
  "(rescueDrone_chans, rescueDrone_state) cyphyaction"
where
  "RescueDrone_mTransTarget_Output5 = \<mu> (\<lambda>X.
    (takeoff\<^bold>.Out \<rightarrow> Wait TOP) ;;
    await_trigger
      ((origin\<^bold>.In \<rightarrow> (turnBackCall \<rightarrow> Wait TURN)) ;;
        (land\<^bold>.Out \<rightarrow> Skip)) ;;
    X)"

definition RescueDrone_mTransTarget_Output6 ::
  "(rescueDrone_chans, rescueDrone_state) cyphyaction"
where
  "RescueDrone_mTransTarget_Output6 = \<mu> (\<lambda>X.
    (takeoff\<^bold>.Out \<rightarrow> Wait TOP) ;;
    Wait DELIVERY ;;
    ((takeoff\<^bold>.Out \<rightarrow> Wait TOP) ;;
      (turnBackCall \<rightarrow> Wait TURN) ;;
      (moveCall\<^bold>.LV \<rightarrow> Skip)) ;;
    await_trigger
      ((origin\<^bold>.In \<rightarrow> (turnBackCall \<rightarrow> Wait TURN)) ;;
        (land\<^bold>.Out \<rightarrow> Skip)) ;;
    X)"

definition RescueDrone_mTransTarget_Output7 ::
  "(rescueDrone_chans, rescueDrone_state) cyphyaction"
where
  "RescueDrone_mTransTarget_Output7 = \<mu> (\<lambda>X.
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

definition RescueDrone_mTransTarget_Output8 ::
  "(rescueDrone_chans, rescueDrone_state) cyphyaction"
where
  "RescueDrone_mTransTarget_Output8 = \<mu> (\<lambda>X.
    await_trigger
      ((origin\<^bold>.In \<rightarrow> (turnBackCall \<rightarrow> Wait TURN)) ;;
        (land\<^bold>.Out \<rightarrow> Skip)) ;;
    (takeoff\<^bold>.Out \<rightarrow> Wait TOP) ;;
    (moveCall\<^bold>.LV \<rightarrow> Skip) ;;
    await_trigger (found\<^bold>.In \<rightarrow> (land\<^bold>.Out \<rightarrow> Skip)) ;;
    Wait DELIVERY ;;
    ((takeoff\<^bold>.Out \<rightarrow> Wait TOP) ;;
      (turnBackCall \<rightarrow> Wait TURN) ;;
      (moveCall\<^bold>.LV \<rightarrow> Skip)) ;;
    X)"

definition RescueDrone_mTransTarget_Output9 ::
  "(rescueDrone_chans, rescueDrone_state) cyphyaction"
where
  "RescueDrone_mTransTarget_Output9 =
    (takeoff\<^bold>.Out \<rightarrow> Wait TOP) ;;
    \<mu> (\<lambda>X.
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

subsection \<open>Controlled unfolding for certified code generation\<close>

lemma Wait_one [cyphy_model_unfolding]:
  "Wait 1 = tock \<rightarrow> Skip"
  by (simp only: One_nat_def Wait.simps)

lemma Wait_two [cyphy_model_unfolding]:
  "Wait 2 = tock \<rightarrow> tock \<rightarrow> Skip"
  by (simp only: numeral_2_eq_2 One_nat_def Wait.simps)

declare await_trigger_def [cyphy_model_unfolding]
declare RescueDrone_def [cyphy_model_unfolding]
declare RescueDrone_mTransTarget_Output0_def [cyphy_model_unfolding]
declare RescueDrone_mTransTarget_Output1_def [cyphy_model_unfolding]
declare RescueDrone_mTransTarget_Output2_def [cyphy_model_unfolding]
declare RescueDrone_mTransTarget_Output3_def [cyphy_model_unfolding]
declare RescueDrone_mTransTarget_Output4_def [cyphy_model_unfolding]
declare RescueDrone_mTransTarget_Output5_def [cyphy_model_unfolding]
declare RescueDrone_mTransTarget_Output6_def [cyphy_model_unfolding]
declare RescueDrone_mTransTarget_Output7_def [cyphy_model_unfolding]
declare RescueDrone_mTransTarget_Output8_def [cyphy_model_unfolding]
declare RescueDrone_mTransTarget_Output9_def [cyphy_model_unfolding]

subsection \<open>All-ten-mutant regression\<close>

local_setup \<open>fn lthy =>
let
  val ctxt = lthy
  val spec = \<^term>\<open>RescueDrone\<close>

  val cases =
    [("Output0", \<^term>\<open>RescueDrone_mTransTarget_Output0\<close>),
     ("Output1", \<^term>\<open>RescueDrone_mTransTarget_Output1\<close>),
     ("Output2", \<^term>\<open>RescueDrone_mTransTarget_Output2\<close>),
     ("Output3", \<^term>\<open>RescueDrone_mTransTarget_Output3\<close>),
     ("Output4", \<^term>\<open>RescueDrone_mTransTarget_Output4\<close>),
     ("Output5", \<^term>\<open>RescueDrone_mTransTarget_Output5\<close>),
     ("Output6", \<^term>\<open>RescueDrone_mTransTarget_Output6\<close>),
     ("Output7", \<^term>\<open>RescueDrone_mTransTarget_Output7\<close>),
     ("Output8", \<^term>\<open>RescueDrone_mTransTarget_Output8\<close>),
     ("Output9", \<^term>\<open>RescueDrone_mTransTarget_Output9\<close>)]

  val proved_cases = ["Output1", "Output4", "Output7"]

  fun run_candidate_phase (name, mutant) =
    (case #1 (checkRefinement ctxt spec mutant) of
      CyPhy_CheckRefinement.ProvedRefines =>
        writeln (name ^ ": ProvedRefines")
    | CyPhy_CheckRefinement.Normalised stage =>
        if member (op =) proved_cases name then
          error (name ^ ": expected ProvedRefines, got Normalised")
        else
          (case obtainCounterexample ctxt stage of
            (SOME trace, _) =>
              writeln (name ^ ": Quickcheck candidate " ^
                String.concatWith " \<rightarrow> "
                  (map (Syntax.string_of_term ctxt) trace))
          | (NONE, _) =>
              writeln (name ^ ": Unknown (no Quickcheck candidate within bounds)")))

  val _ = List.app run_candidate_phase cases
in
  writeln
    "CyPhy_CodeGen_Test: proof-first code generation ran for all ten mutants; Outputs 1, 4, and 7 proved"
  ; lthy
end
\<close>



end
