theory RescueDrone
  imports "../TestGen"
begin

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

record_default rescueDrone_state

fun Wait :: "nat \<Rightarrow> (rescueDrone_chans, 'st) cyphyaction" where
  "Wait 0 = Skip" |
  "Wait (Suc n) = tock \<rightarrow> (Wait n)"

definition await_trigger :: "(rescueDrone_chans, 'st) cyphyaction \<Rightarrow> (rescueDrone_chans, 'st) cyphyaction" where
  [rct_defs]: "await_trigger P = \<nu> (\<lambda> X. P \<box> tock \<rightarrow> X)"

abbreviation DELIVERY :: "\<nat>" where "DELIVERY \<equiv> 2"
abbreviation LV :: "\<nat>" where "LV \<equiv> 1"
abbreviation TOP :: "\<nat>" where "TOP \<equiv> 1"
abbreviation TURN :: "\<nat>" where "TURN \<equiv> 1"
abbreviation tockLength :: "\<real>" where "tockLength \<equiv> 1"
abbreviation timeStep :: "\<real>" where "timeStep \<equiv> 0.1"
(* abbreviation arena :: "arena" where "arena " *)

dataspace RescueDrone_RoboChart =
  constants
    DELIVERY :: "\<nat>"
    LV :: "\<nat>"
    TOP :: "\<nat>"
    TURN :: "\<nat>"

recursive RescueDrone :: "(rescueDrone_chans, rescueDrone_state) cyphyaction" where
  "RescueDrone =
    (takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; 
    (moveCall\<^bold>.LV \<rightarrow> Skip) ;;
    await_trigger(found\<^bold>.In \<rightarrow> (land\<^bold>.Out \<rightarrow> Skip)) ;; 
    (Wait(DELIVERY)) ;;
    ((takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; (turnBackCall \<rightarrow> Wait(TURN)) ;; (moveCall\<^bold>.LV \<rightarrow> Skip)) ;;
    await_trigger((origin\<^bold>.In \<rightarrow> (turnBackCall \<rightarrow> Wait(TURN))) ;; (land\<^bold>.Out \<rightarrow> Skip)) ;;
    RescueDrone"

recursive RescueDrone_mTransTarget_Output0 :: "(rescueDrone_chans, rescueDrone_state) cyphyaction" where
  "RescueDrone_mTransTarget_Output0 =
    (takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; 
    (Wait(DELIVERY)) ;;
    ((takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; (turnBackCall \<rightarrow> Wait(TURN)) ;; (moveCall\<^bold>.LV \<rightarrow> Skip)) ;;
    await_trigger((origin\<^bold>.In \<rightarrow> (turnBackCall \<rightarrow> Wait(TURN))) ;; (land\<^bold>.Out \<rightarrow> Skip)) ;;
    RescueDrone_mTransTarget_Output0"

recursive RescueDrone_mTransTarget_Output1 :: "(rescueDrone_chans, rescueDrone_state) cyphyaction" where
  "RescueDrone_mTransTarget_Output1 =
    (takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; 
    (moveCall\<^bold>.LV \<rightarrow> Skip) ;;
    await_trigger(found\<^bold>.In \<rightarrow> (land\<^bold>.Out \<rightarrow> Skip)) ;; 
    (Wait(DELIVERY)) ;;
    ((takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; (turnBackCall \<rightarrow> Wait(TURN)) ;; (moveCall\<^bold>.LV \<rightarrow> Skip)) ;;
    await_trigger((origin\<^bold>.In \<rightarrow> (turnBackCall \<rightarrow> Wait(TURN))) ;; (land\<^bold>.Out \<rightarrow> Skip)) ;;
    RescueDrone_mTransTarget_Output1"

recursive RescueDrone_mTransTarget_Output2 :: "(rescueDrone_chans, rescueDrone_state) cyphyaction" where
  "RescueDrone_mTransTarget_Output2 =
    (takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; 
    RescueDrone_mTransTarget_Output2"

recursive RescueDrone_mTransTarget_Output3  :: "(rescueDrone_chans, rescueDrone_state) cyphyaction"
    and RescueDrone_mTransTarget_Output3_2  :: "(rescueDrone_chans, rescueDrone_state) cyphyaction" where
  "RescueDrone_mTransTarget_Output3 = 
    (takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; 
    (moveCall\<^bold>.LV \<rightarrow> Skip) ;;
    await_trigger(found\<^bold>.In \<rightarrow> (land\<^bold>.Out \<rightarrow> Skip)) ;; RescueDrone_mTransTarget_Output3_2"
| "RescueDrone_mTransTarget_Output3_2 =
    (Wait(DELIVERY)) ;;
    ((takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; (turnBackCall \<rightarrow> Wait(TURN)) ;; (moveCall\<^bold>.LV \<rightarrow> Skip)) ;;
    RescueDrone_mTransTarget_Output3_2"

recursive RescueDrone_mTransTarget_Output4  :: "(rescueDrone_chans, rescueDrone_state) cyphyaction" where
  "RescueDrone_mTransTarget_Output4 =
    (takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; 
    (moveCall\<^bold>.LV \<rightarrow> Skip) ;;
    await_trigger(found\<^bold>.In \<rightarrow> (land\<^bold>.Out \<rightarrow> Skip)) ;; 
    (Wait(DELIVERY)) ;;
    ((takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; (turnBackCall \<rightarrow> Wait(TURN)) ;; (moveCall\<^bold>.LV \<rightarrow> Skip)) ;;
    await_trigger((origin\<^bold>.In \<rightarrow> (turnBackCall \<rightarrow> Wait(TURN))) ;; (land\<^bold>.Out \<rightarrow> Skip)) ;;
    RescueDrone_mTransTarget_Output4"

recursive RescueDrone_mTransTarget_Output5  :: "(rescueDrone_chans, rescueDrone_state) cyphyaction" where
  "RescueDrone_mTransTarget_Output5 =
    (takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; 
    await_trigger((origin\<^bold>.In \<rightarrow> (turnBackCall \<rightarrow> Wait(TURN))) ;; (land\<^bold>.Out \<rightarrow> Skip)) ;;
    RescueDrone_mTransTarget_Output5"

recursive RescueDrone_mTransTarget_Output6  :: "(rescueDrone_chans, rescueDrone_state) cyphyaction" where
  "RescueDrone_mTransTarget_Output6 =
    (takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; 
    (Wait(DELIVERY)) ;;
    ((takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; (turnBackCall \<rightarrow> Wait(TURN)) ;; (moveCall\<^bold>.LV \<rightarrow> Skip)) ;;
    await_trigger((origin\<^bold>.In \<rightarrow> (turnBackCall \<rightarrow> Wait(TURN))) ;; (land\<^bold>.Out \<rightarrow> Skip)) ;;
    RescueDrone_mTransTarget_Output6"

recursive RescueDrone_mTransTarget_Output7  :: "(rescueDrone_chans, rescueDrone_state) cyphyaction" where
  "RescueDrone_mTransTarget_Output7 =
    (takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; 
    (moveCall\<^bold>.LV \<rightarrow> Skip) ;;
    await_trigger(found\<^bold>.In \<rightarrow> (land\<^bold>.Out \<rightarrow> Skip)) ;; 
    (Wait(DELIVERY)) ;;
    ((takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; (turnBackCall \<rightarrow> Wait(TURN)) ;; (moveCall\<^bold>.LV \<rightarrow> Skip)) ;;
    await_trigger((origin\<^bold>.In \<rightarrow> (turnBackCall \<rightarrow> Wait(TURN))) ;; (land\<^bold>.Out \<rightarrow> Skip)) ;;
    RescueDrone_mTransTarget_Output7"

recursive RescueDrone_mTransTarget_Output8  :: "(rescueDrone_chans, rescueDrone_state) cyphyaction" where
  "RescueDrone_mTransTarget_Output8 =
    await_trigger((origin\<^bold>.In \<rightarrow> (turnBackCall \<rightarrow> Wait(TURN))) ;; (land\<^bold>.Out \<rightarrow> Skip)) ;;
    (takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; 
    (moveCall\<^bold>.LV \<rightarrow> Skip) ;;
    await_trigger(found\<^bold>.In \<rightarrow> (land\<^bold>.Out \<rightarrow> Skip)) ;; 
    (Wait(DELIVERY)) ;;
    ((takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; (turnBackCall \<rightarrow> Wait(TURN)) ;; (moveCall\<^bold>.LV \<rightarrow> Skip)) ;;
    RescueDrone_mTransTarget_Output8"

recursive RescueDrone_mTransTarget_Output9  :: "(rescueDrone_chans, rescueDrone_state) cyphyaction"
    and RescueDrone_mTransTarget_Output9_2  :: "(rescueDrone_chans, rescueDrone_state) cyphyaction" where
  "RescueDrone_mTransTarget_Output9 = 
    (takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; RescueDrone_mTransTarget_Output9_2"
| "RescueDrone_mTransTarget_Output9_2 =
    (moveCall\<^bold>.LV \<rightarrow> Skip) ;;
    await_trigger(found\<^bold>.In \<rightarrow> (land\<^bold>.Out \<rightarrow> Skip)) ;; 
    (Wait(DELIVERY)) ;;
    ((takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; (turnBackCall \<rightarrow> Wait(TURN)) ;; (moveCall\<^bold>.LV \<rightarrow> Skip)) ;;
    await_trigger((origin\<^bold>.In \<rightarrow> (turnBackCall \<rightarrow> Wait(TURN))) ;; (land\<^bold>.Out \<rightarrow> Skip)) ;;
    RescueDrone_mTransTarget_Output9_2"

declare [[testgen_timeout=5000]]

ML \<open>obtainCounterexample @{context}
      @{term "RescueDrone :: (rescueDrone_chans, rescueDrone_state) cyphyaction"}
      @{term "RescueDrone_mTransTarget_Output0 :: (rescueDrone_chans, rescueDrone_state) cyphyaction"}\<close>


ML \<open>obtainCounterexample @{context}
      @{term "RescueDrone :: (rescueDrone_chans, rescueDrone_state) cyphyaction"}
      @{term "RescueDrone_mTransTarget_Output1 :: (rescueDrone_chans, rescueDrone_state) cyphyaction"}\<close>


ML \<open>obtainCounterexample @{context}
      @{term "RescueDrone :: (rescueDrone_chans, rescueDrone_state) cyphyaction"}
      @{term "RescueDrone_mTransTarget_Output2 :: (rescueDrone_chans, rescueDrone_state) cyphyaction"}\<close>

ML \<open>obtainCounterexample @{context}
      @{term "RescueDrone :: (rescueDrone_chans, rescueDrone_state) cyphyaction"}
      @{term "RescueDrone_mTransTarget_Output3 :: (rescueDrone_chans, rescueDrone_state) cyphyaction"}\<close>

ML \<open>obtainCounterexample @{context}
      @{term "RescueDrone :: (rescueDrone_chans, rescueDrone_state) cyphyaction"}
      @{term "RescueDrone_mTransTarget_Output4 :: (rescueDrone_chans, rescueDrone_state) cyphyaction"}\<close>


ML \<open>obtainCounterexample @{context}
      @{term "RescueDrone :: (rescueDrone_chans, rescueDrone_state) cyphyaction"}
      @{term "RescueDrone_mTransTarget_Output5 :: (rescueDrone_chans, rescueDrone_state) cyphyaction"}\<close>


ML \<open>obtainCounterexample @{context}
      @{term "RescueDrone :: (rescueDrone_chans, rescueDrone_state) cyphyaction"}
      @{term "RescueDrone_mTransTarget_Output6 :: (rescueDrone_chans, rescueDrone_state) cyphyaction"}\<close>

ML \<open>obtainCounterexample @{context}
      @{term "RescueDrone :: (rescueDrone_chans, rescueDrone_state) cyphyaction"}
      @{term "RescueDrone_mTransTarget_Output7 :: (rescueDrone_chans, rescueDrone_state) cyphyaction"}\<close>

ML \<open>obtainCounterexample @{context}
      @{term "RescueDrone :: (rescueDrone_chans, rescueDrone_state) cyphyaction"}
      @{term "RescueDrone_mTransTarget_Output8 :: (rescueDrone_chans, rescueDrone_state) cyphyaction"}\<close>

ML \<open>obtainCounterexample @{context}
      @{term "RescueDrone :: (rescueDrone_chans, rescueDrone_state) cyphyaction"}
      @{term "RescueDrone_mTransTarget_Output9 :: (rescueDrone_chans, rescueDrone_state) cyphyaction"}\<close>

section \<open>RoboWorld\<close>

record arena =
    origin_region :: "(real * real * real)"
    target_region :: "(real * real * real)"

definition EnvironmentInit :: "arena \<Rightarrow> (rescueDrone_chans, rescueDrone_state) cyphyaction" where
  "EnvironmentInit arena   = pos := origin_region arena"

definition RobotMovement :: "(rescueDrone_chans, rescueDrone_state) cyphyaction" where
  "RobotMovement = [\<Lambda> pos` = vel, vel` = acc, ori` = angVel, angVel` = angAcc, stepTimer` = 1]"

definition RobotMovementAction :: "(rescueDrone_chans, rescueDrone_state) cyphyaction" where
  "RobotMovementAction = RobotMovement \<triangle>\<^sub>p (stepTimer \<ge> timeStep)"
term dist
definition found_InputEventTrigger :: "arena \<Rightarrow> (rescueDrone_chans, rescueDrone_state) cyphyaction" where
  "found_InputEventTrigger arena = foundTriggered\<^bold>!(dist pos (target_region arena) \<le> 0.25) \<rightarrow> Skip"

definition origin_InputEventTrigger :: "arena \<Rightarrow> (rescueDrone_chans, rescueDrone_state) cyphyaction" where
  "origin_InputEventTrigger arena = originTriggered\<^bold>!(dist pos (origin_region arena) \<le> 0.25) \<rightarrow> Skip"

definition InputTriggers :: "arena \<Rightarrow> (rescueDrone_chans, rescueDrone_state) cyphyaction" where
  "InputTriggers arena = found_InputEventTrigger arena \<lbrakk> \<^bold>0 | \<lbrace>\<rbrace> | \<^bold>0 \<rbrakk> origin_InputEventTrigger arena"


definition Communication :: "(rescueDrone_chans, rescueDrone_state) cyphyaction" where
  "Communication = \<mu> (\<lambda> X.
    (setVel\<^bold>?v \<rightarrow> (vel := v) ;; X)
     \<box>
    (setAngVel\<^bold>?av \<rightarrow> (angVel := av) ;; X)
     \<box>
    proceed \<rightarrow> Skip)"

recursive EnvironmentLoop :: "arena \<Rightarrow> (rescueDrone_chans, rescueDrone_state) cyphyaction" where
  "EnvironmentLoop arena =
    RobotMovementAction ;;
    InputTriggers arena ;;
    Communication ;;
    (stepTimer := 0) ;;
    if tockTimer \<ge> tockLength then tockTimer := 0 else Skip fi ;; (EnvironmentLoop arena)"

definition found_Buffer :: "(rescueDrone_chans, rescueDrone_state) cyphyaction" where
  "found_Buffer =
    foundTrig := False ;; \<mu> (\<lambda> X. (
      foundTriggered\<^bold>?b \<rightarrow> (foundTrig := b)
       \<box>
      (foundTrig) \<^bold>& found\<^bold>.In \<rightarrow> Skip
    ) ;; X)"

definition origin_Buffer :: "(rescueDrone_chans, rescueDrone_state) cyphyaction" where
  "origin_Buffer =
    originTrig := False ;; \<mu> (\<lambda> X. (
      originTriggered\<^bold>?b \<rightarrow> (originTrig := b)
       \<box>
      (originTrig) \<^bold>& origin\<^bold>!In \<rightarrow> Skip
    ) ;; X)"

definition InputBuffers :: "(rescueDrone_chans, rescueDrone_state) cyphyaction" where
  "InputBuffers = found_Buffer \<lbrakk> foundTrig | \<lbrace>\<rbrace> | originTrig \<rbrakk> origin_Buffer"

definition Environment :: "arena \<Rightarrow> (rescueDrone_chans, rescueDrone_state) cyphyaction" where
  "Environment arena =
    (EnvironmentInit arena ;; EnvironmentLoop arena)
      \<lbrakk> (pos, vel, acc, ori, angVel, angAcc, stepTimer, tockTimer) 
        | \<lbrace> foundTriggered, originTriggered \<rbrace> |
      (foundTrig, originTrig) \<rbrakk>
    InputBuffers"

definition oriToVec :: "real*real*real \<Rightarrow> real*real*real" where
  "oriToVec = (\<lambda>(yaw, pitch, roll). ((cos yaw) * (cos pitch), (sin yaw) * (cos pitch), -sin pitch))"

definition move_OperationMapping :: "(rescueDrone_chans, rescueDrone_state) cyphyaction" where
  "move_OperationMapping = \<mu> (\<lambda> X.
    moveCall\<^bold>?lv \<rightarrow> setVel\<^bold>!(real lv *\<^sub>R oriToVec ori) \<rightarrow> X
     \<box>
    proceed \<rightarrow> X)"

definition turnBack_OperationMapping :: "(rescueDrone_chans, rescueDrone_state) cyphyaction" where
  "turnBack_OperationMapping = \<mu> (\<lambda> X.
    turnBackCall
      \<rightarrow> setVel\<^bold>!(0, 0, 0) 
      \<rightarrow> setAngVel\<^bold>!(pi, 0, 0)
      \<rightarrow> (tock
      \<rightarrow> setAngVel\<^bold>!(0, 0, 0)
      \<rightarrow> X)
     \<box>
    proceed \<rightarrow> X)"

definition takeoff_OutputEventMapping :: "(rescueDrone_chans, rescueDrone_state) cyphyaction" where
  "takeoff_OutputEventMapping = \<mu> (\<lambda> X.
    takeoff\<^bold>.Out \<rightarrow> setVel\<^bold>!(0, 0, 1) \<rightarrow> X
     \<box>
    (proceed \<rightarrow> X))"

definition land_OutputEventMapping :: "(rescueDrone_chans, rescueDrone_state) cyphyaction" where
  "land_OutputEventMapping = \<mu> (\<lambda> X.
    land\<^bold>.Out \<rightarrow> setVel\<^bold>!(0, 0, -1) \<rightarrow> X
     \<box>
    (proceed \<rightarrow> X))"

definition Mapping :: "(rescueDrone_chans, rescueDrone_state) cyphyaction" where
  "Mapping =
    move_OperationMapping
      \<lbrakk> \<^bold>0 | \<lbrace>\<rbrace> | \<^bold>0 \<rbrakk>
    (turnBack_OperationMapping
      \<lbrakk> \<^bold>0 | \<lbrace>\<rbrace> | \<^bold>0 \<rbrakk>
    (takeoff_OutputEventMapping
      \<lbrakk> \<^bold>0 | \<lbrace>\<rbrace> | \<^bold>0 \<rbrakk>
    land_OutputEventMapping))"


definition RescueRoboWorld :: "arena \<Rightarrow> (rescueDrone_chans, rescueDrone_state) cyphyaction" where
  "RescueRoboWorld arena = Environment arena \<lbrakk> \<^bold>v | \<lbrace> setVel, setAngVel, proceed \<rbrace> | \<^bold>0 \<rbrakk> Mapping"

definition RescueRoboWorld_pred :: "arena \<Rightarrow> bool" where
  "RescueRoboWorld_pred arena = (dist (target_region arena) (origin_region arena) \<le> 2)"

section \<open>Applying the test generation\<close>

generate_tests_rct[testgen_timeout=5000, testgen_verbose=true]
  RoboChart = RescueDrone
  Mutants =
    RescueDrone_mTransTarget_Output0,
    RescueDrone_mTransTarget_Output1,
    RescueDrone_mTransTarget_Output2,
    RescueDrone_mTransTarget_Output3,
    RescueDrone_mTransTarget_Output4,
    RescueDrone_mTransTarget_Output5,
    RescueDrone_mTransTarget_Output6,
    RescueDrone_mTransTarget_Output7,
    RescueDrone_mTransTarget_Output8,
    RescueDrone_mTransTarget_Output9
  RoboWorld = RescueRoboWorld RescueRoboWorld_pred
  Iterations = 1