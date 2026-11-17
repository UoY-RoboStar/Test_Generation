theory RescueDrone
  imports "Test_Generation.TestGen" "HOL-Library.Code_Target_Int"
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
abbreviation timeStep :: "\<real>" where "timeStep \<equiv> Scaled 100000000"
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
  [rct_defs]: "EnvironmentInit arena   = pos := origin_region arena"

definition RobotMovement :: "(rescueDrone_chans, rescueDrone_state) cyphyaction" where
  [rct_defs]: "RobotMovement = [\<Lambda> pos` = vel, vel` = acc, ori` = angVel, angVel` = angAcc, stepTimer` = 1, tockTimer` = 1]"

definition RobotMovementAction :: "(rescueDrone_chans, rescueDrone_state) cyphyaction" where
  [rct_defs]: "RobotMovementAction = RobotMovement \<triangle>\<^sub>p (stepTimer \<ge> timeStep)"

definition dist3_sq :: "(real \<times> real \<times> real) \<Rightarrow> (real \<times> real \<times> real) \<Rightarrow> real" where
  "dist3_sq p1 p2 = (case (p1, p2) of ((x1, y1, z1), (x2, y2, z2)) \<Rightarrow> (x1 - x2)\<^sup>2 + (y1 - y2)\<^sup>2 + (z1 - z2)\<^sup>2)"

definition found_InputEventTrigger :: "arena \<Rightarrow> (rescueDrone_chans, rescueDrone_state) cyphyaction" where
  [rct_defs]: "found_InputEventTrigger arena = foundTriggered\<^bold>!(dist3_sq pos (target_region arena) \<le> 0.25\<^sup>2) \<rightarrow> Skip"

definition origin_InputEventTrigger :: "arena \<Rightarrow> (rescueDrone_chans, rescueDrone_state) cyphyaction" where
  [rct_defs]: "origin_InputEventTrigger arena = originTriggered\<^bold>!(dist3_sq pos (origin_region arena) \<le> 0.25\<^sup>2) \<rightarrow> Skip"

definition InputTriggers :: "arena \<Rightarrow> (rescueDrone_chans, rescueDrone_state) cyphyaction" where
  [rct_defs]: "InputTriggers arena = found_InputEventTrigger arena ;; origin_InputEventTrigger arena"


recursive Communication :: "(rescueDrone_chans, rescueDrone_state) cyphyaction" where
  "Communication =
    (((setVel\<^bold>?v \<rightarrow> (vel := v))
     \<box>
    (setAngVel\<^bold>?av \<rightarrow> (angVel := av))) ;; Communication)
     \<box>
    proceed \<rightarrow> Skip"


lemmas [simp] = Communication_def
recursive EnvironmentLoop :: "arena \<Rightarrow> (rescueDrone_chans, rescueDrone_state) cyphyaction" where
  "EnvironmentLoop arena =
    RobotMovementAction ;;
    InputTriggers arena ;;
    Communication ;;
    (stepTimer := 0) ;;
    if tockTimer \<ge> tockLength then tock \<rightarrow> tockTimer := 0 else Skip fi ;; EnvironmentLoop arena"
lemmas [simp del] = Communication_def

recursive 
    found_Buffer :: "(rescueDrone_chans, rescueDrone_state) cyphyaction" 
and found_Buffer_loop :: "(rescueDrone_chans, rescueDrone_state) cyphyaction"
where
  "found_Buffer =
    foundTrig := False ;; found_Buffer_loop"
| "found_Buffer_loop =
    (
      foundTriggered\<^bold>?b \<rightarrow> (foundTrig := b)
       \<box>
      (foundTrig) \<^bold>& found\<^bold>.In \<rightarrow> Skip
    ) ;; found_Buffer_loop"

recursive 
    origin_Buffer :: "(rescueDrone_chans, rescueDrone_state) cyphyaction" 
and origin_Buffer_loop :: "(rescueDrone_chans, rescueDrone_state) cyphyaction"
where
  "origin_Buffer =
    originTrig := False ;; origin_Buffer_loop"
| "origin_Buffer_loop =
    (
      originTriggered\<^bold>?b \<rightarrow> (originTrig := b)
       \<box>
      (originTrig) \<^bold>& origin\<^bold>.In \<rightarrow> Skip
    ) ;; origin_Buffer_loop"

definition InputBuffers :: "(rescueDrone_chans, rescueDrone_state) cyphyaction" where
  [rct_defs]: "InputBuffers = found_Buffer \<lbrakk> foundTrig | \<lbrace>\<rbrace> | originTrig \<rbrakk> origin_Buffer"
term Hide
definition Environment :: "arena \<Rightarrow> (rescueDrone_chans, rescueDrone_state) cyphyaction" where
  [rct_defs]: "Environment arena =
    ((EnvironmentInit arena ;; EnvironmentLoop arena)
      \<lbrakk> (pos, vel, acc, ori, angVel, angAcc, stepTimer, tockTimer) 
        | \<lbrace> foundTriggered, originTriggered \<rbrace>\<^sub>f |
      (foundTrig, originTrig) \<rbrakk>
    InputBuffers) \<Zhide> \<lbrace> foundTriggered, originTriggered \<rbrace>\<^sub>f"

fun cos_approx :: "nat \<Rightarrow> real \<Rightarrow> real" where
  "cos_approx n x = (if n = 0 then cos_coeff 0 else (cos_coeff n) * x^n + cos_approx (n-1) x)"
fun sin_approx :: "nat \<Rightarrow> real \<Rightarrow> real" where
  "sin_approx n x = (if n = 0 then sin_coeff 0 else (sin_coeff n) * x^n + sin_approx (n-1) x)"

fun atan_coeff :: "nat \<Rightarrow> real" where
  "atan_coeff n = (if even n then 0 else (- 1) ^ ((n - Suc 0) div 2) / n)"
fun atan_approx :: "nat \<Rightarrow> real \<Rightarrow> real" where
  "atan_approx n x = (if n = 0 then atan_coeff 0 else (atan_coeff n) * x^n + atan_approx (n-1) x)"
fun pi_approx :: "nat \<Rightarrow> real" where
  "pi_approx n = 4 * (4 * atan_approx n (1 / 5) - atan_approx n (1 / 239))"

definition oriToVec :: "real*real*real \<Rightarrow> real*real*real" where
  [rct_defs]: "oriToVec = (\<lambda>(yaw, pitch, roll). ((cos_approx 10 yaw) * (cos_approx 10 pitch), (sin_approx 10 yaw) * (cos_approx 10 pitch), -sin_approx 10 pitch))"

recursive move_OperationMapping :: "(rescueDrone_chans, rescueDrone_state) cyphyaction" where
  "move_OperationMapping = 
    (moveCall\<^bold>?lv \<rightarrow> setVel\<^bold>!(real lv *\<^sub>R oriToVec ori) \<rightarrow> move_OperationMapping)
     \<box>
    (proceed \<rightarrow> move_OperationMapping)"

recursive turnBack_OperationMapping :: "(rescueDrone_chans, rescueDrone_state) cyphyaction" where
  "turnBack_OperationMapping = 
    (turnBackCall
      \<rightarrow> setVel\<^bold>!(0, 0, 0) 
      \<rightarrow> setAngVel\<^bold>!(pi_approx 10, 0, 0)
      \<rightarrow> tock
      \<rightarrow> setAngVel\<^bold>!(0, 0, 0)
      \<rightarrow> turnBack_OperationMapping)
     \<box>
    (proceed \<rightarrow> turnBack_OperationMapping)"

recursive takeoff_OutputEventMapping :: "(rescueDrone_chans, rescueDrone_state) cyphyaction" where
  "takeoff_OutputEventMapping =
    (takeoff\<^bold>.Out \<rightarrow> setVel\<^bold>!(0, 0, 1) \<rightarrow> takeoff_OutputEventMapping)
     \<box>
    (proceed \<rightarrow> takeoff_OutputEventMapping)"

recursive land_OutputEventMapping :: "(rescueDrone_chans, rescueDrone_state) cyphyaction" where
  "land_OutputEventMapping =
    (land\<^bold>.Out \<rightarrow> setVel\<^bold>!(0, 0, -1) \<rightarrow> land_OutputEventMapping)
     \<box>
    (proceed \<rightarrow> land_OutputEventMapping)"

definition Mapping :: "(rescueDrone_chans, rescueDrone_state) cyphyaction" where
  [rct_defs]: "Mapping =
    move_OperationMapping
      \<lbrakk> \<^bold>0 | \<lbrace>proceed\<rbrace> | \<^bold>0 \<rbrakk>
    (turnBack_OperationMapping
      \<lbrakk> \<^bold>0 | \<lbrace>proceed\<rbrace> | \<^bold>0 \<rbrakk>
    (takeoff_OutputEventMapping
      \<lbrakk> \<^bold>0 | \<lbrace>proceed\<rbrace> | \<^bold>0 \<rbrakk>
    land_OutputEventMapping))"

unbundle no UTP_Syntax


definition RescueRoboWorld :: "arena \<Rightarrow> (rescueDrone_chans, rescueDrone_state) cyphyaction" where
  [rct_defs]: "RescueRoboWorld arena =
    (Environment arena \<lbrakk> \<^bold>v | \<lbrace> setVel, setAngVel, proceed \<rbrace>\<^sub>f | \<^bold>0 \<rbrakk> Mapping) \<Zhide> \<lbrace> setVel, setAngVel, proceed \<rbrace>\<^sub>f"

definition on_ground_pred :: "arena \<Rightarrow> bool" where
  "on_ground_pred arena = ((snd o snd) (target_region arena) = 0 \<and> (snd o snd) (origin_region arena) = 0)"

definition RescueRoboWorld_pred :: "arena \<Rightarrow> bool" where
  "RescueRoboWorld_pred arena = (on_ground_pred arena \<and> (dist3_sq (target_region arena) (origin_region arena) \<ge> 2\<^sup>2))"

section \<open>Applying the test generation\<close>

declare [[testgen_loop_unroll_limit=20]]
declare [[testgen_step_limit=10000]]
declare [[testgen_timestep="1/10"]]

generate_tests_rct[testgen_timeout=10000, testgen_verbose=true, testgen_consts_breadth=10]
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
  Iterations = 2
