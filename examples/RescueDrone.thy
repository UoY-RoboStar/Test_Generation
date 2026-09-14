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

print_theorems
find_consts "natural \<Rightarrow> 'a"

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
print_theorems

definition await_trigger :: "(rescueDrone_chans, 'st) cyphyaction \<Rightarrow> (rescueDrone_chans, 'st) cyphyaction" where
  [rct_defs]: "await_trigger P = \<nu> (\<lambda> X. P \<box> tock \<rightarrow> X)"

record arena =
    origin_region :: "(real * real * real) set"
    target_region :: "(real * real * real) set"


abbreviation DELIVERY :: "\<nat>" where "DELIVERY \<equiv> 2"
abbreviation LV :: "\<nat>" where "LV \<equiv> 1"
abbreviation TOP :: "\<nat>" where "TOP \<equiv> 1"
abbreviation TURN :: "\<nat>" where "TURN \<equiv> 1"
abbreviation tockLength :: "\<real>" where "tockLength \<equiv> 1"
abbreviation timeStep :: "\<real>" where "timeStep \<equiv> 0.1"
(* abbreviation arena :: "arena" where "arena " *)


recursive where
  "RescueDrone =
    (takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; 
    (moveCall\<^bold>.LV \<rightarrow> Skip) ;;
    await_trigger(found\<^bold>.In \<rightarrow> (land\<^bold>.Out \<rightarrow> Skip)) ;; 
    (Wait(DELIVERY)) ;;
    ((takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; (turnBackCall \<rightarrow> Wait(TURN)) ;; (moveCall\<^bold>.LV \<rightarrow> Skip)) ;;
    await_trigger((origin\<^bold>.In \<rightarrow> (turnBackCall \<rightarrow> Wait(TURN))) ;; (land\<^bold>.Out \<rightarrow> Skip)) ;;
    RescueDrone"

recursive where
  "RescueDrone_mTransTarget_Output0 =
    (takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; 
    (Wait(DELIVERY)) ;;
    ((takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; (turnBackCall \<rightarrow> Wait(TURN)) ;; (moveCall\<^bold>.LV \<rightarrow> Skip)) ;;
    await_trigger((origin\<^bold>.In \<rightarrow> (turnBackCall \<rightarrow> Wait(TURN))) ;; (land\<^bold>.Out \<rightarrow> Skip)) ;;
    RescueDrone_mTransTarget_Output0"

recursive where
  "RescueDrone_mTransTarget_Output1 =
    (takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; 
    (moveCall\<^bold>.LV \<rightarrow> Skip) ;;
    await_trigger(found\<^bold>.In \<rightarrow> (land\<^bold>.Out \<rightarrow> Skip)) ;; 
    (Wait(DELIVERY)) ;;
    ((takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; (turnBackCall \<rightarrow> Wait(TURN)) ;; (moveCall\<^bold>.LV \<rightarrow> Skip)) ;;
    await_trigger((origin\<^bold>.In \<rightarrow> (turnBackCall \<rightarrow> Wait(TURN))) ;; (land\<^bold>.Out \<rightarrow> Skip)) ;;
    RescueDrone_mTransTarget_Output1"

recursive where
  "RescueDrone_mTransTarget_Output2 =
    (takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; 
    RescueDrone_mTransTarget_Output2"

recursive where
  "RescueDrone_mTransTarget_Output3 = 
    (takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; 
    (moveCall\<^bold>.LV \<rightarrow> Skip) ;;
    await_trigger(found\<^bold>.In \<rightarrow> (land\<^bold>.Out \<rightarrow> Skip)) ;; RescueDrone_mTransTarget_Output3_2"
| "RescueDrone_mTransTarget_Output3_2 =
    (Wait(DELIVERY)) ;;
    ((takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; (turnBackCall \<rightarrow> Wait(TURN)) ;; (moveCall\<^bold>.LV \<rightarrow> Skip)) ;;
    RescueDrone_mTransTarget_Output3_2"

recursive where
  "RescueDrone_mTransTarget_Output4 =
    (takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; 
    (moveCall\<^bold>.LV \<rightarrow> Skip) ;;
    await_trigger(found\<^bold>.In \<rightarrow> (land\<^bold>.Out \<rightarrow> Skip)) ;; 
    (Wait(DELIVERY)) ;;
    ((takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; (turnBackCall \<rightarrow> Wait(TURN)) ;; (moveCall\<^bold>.LV \<rightarrow> Skip)) ;;
    await_trigger((origin\<^bold>.In \<rightarrow> (turnBackCall \<rightarrow> Wait(TURN))) ;; (land\<^bold>.Out \<rightarrow> Skip)) ;;
    RescueDrone_mTransTarget_Output4"

recursive where
  "RescueDrone_mTransTarget_Output5 =
    (takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; 
    await_trigger((origin\<^bold>.In \<rightarrow> (turnBackCall \<rightarrow> Wait(TURN))) ;; (land\<^bold>.Out \<rightarrow> Skip)) ;;
    RescueDrone_mTransTarget_Output5"

recursive where
  "RescueDrone_mTransTarget_Output6 =
    (takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; 
    (Wait(DELIVERY)) ;;
    ((takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; (turnBackCall \<rightarrow> Wait(TURN)) ;; (moveCall\<^bold>.LV \<rightarrow> Skip)) ;;
    await_trigger((origin\<^bold>.In \<rightarrow> (turnBackCall \<rightarrow> Wait(TURN))) ;; (land\<^bold>.Out \<rightarrow> Skip)) ;;
    RescueDrone_mTransTarget_Output6"

recursive where
  "RescueDrone_mTransTarget_Output7 =
    (takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; 
    (moveCall\<^bold>.LV \<rightarrow> Skip) ;;
    await_trigger(found\<^bold>.In \<rightarrow> (land\<^bold>.Out \<rightarrow> Skip)) ;; 
    (Wait(DELIVERY)) ;;
    ((takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; (turnBackCall \<rightarrow> Wait(TURN)) ;; (moveCall\<^bold>.LV \<rightarrow> Skip)) ;;
    await_trigger((origin\<^bold>.In \<rightarrow> (turnBackCall \<rightarrow> Wait(TURN))) ;; (land\<^bold>.Out \<rightarrow> Skip)) ;;
    RescueDrone_mTransTarget_Output7"

recursive where
  "RescueDrone_mTransTarget_Output8 =
    await_trigger((origin\<^bold>.In \<rightarrow> (turnBackCall \<rightarrow> Wait(TURN))) ;; (land\<^bold>.Out \<rightarrow> Skip)) ;;
    (takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; 
    (moveCall\<^bold>.LV \<rightarrow> Skip) ;;
    await_trigger(found\<^bold>.In \<rightarrow> (land\<^bold>.Out \<rightarrow> Skip)) ;; 
    (Wait(DELIVERY)) ;;
    ((takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; (turnBackCall \<rightarrow> Wait(TURN)) ;; (moveCall\<^bold>.LV \<rightarrow> Skip)) ;;
    RescueDrone_mTransTarget_Output8"

recursive where
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