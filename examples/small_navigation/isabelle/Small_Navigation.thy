theory Small_Navigation
  imports "Test_Generation.Ax_CyPhyCircus" Action_Command_Compat
begin

(* Changed the import from Axiomatic_Circus, which is not available, to Ax_CyPhyCircus and Action_Command_Compat. *)

subsection \<open> Prelude \<close>

(* Changed lit_vars to declare [[literal_variables]] because lit_vars could not be found in the imported library. *)
declare [[literal_variables]]
unbundle Circus_Syntax

hide_const (open) sum

subsection \<open> Model \<close>


	
	
datatype NIDS_Navigation_small_navigation = 
	NID_i0_Navigation_small_navigation | 
	NID_WaitTarget_Navigation_small_navigation | 
	NID_WaitForPose_Navigation_small_navigation | 
	NID_CheckPosition_Navigation_small_navigation | 
	NID_WaitMoveApplied_Navigation_small_navigation | 
	NID_WaitStopApplied_Navigation_small_navigation | 
	NID_f0_Navigation_small_navigation



\<comment> \<open>Channel Declaration\<close>
(* Removed the | lines between channel groups because chantype does not accept them. *)
chantype mychan = 
share :: unit
\<comment> \<open>terminate_channel\<close>

terminate :: unit 
\<comment> \<open>internal_channel_stmbd_Navigation_small_navigation\<close>

internal__Navigation_small_navigation :: "NIDS_Navigation_small_navigation"
\<comment> \<open>flowchannel_stmbd_Navigation_small_navigation\<close>

interrupt_Navigation_small_navigation :: unit 
exited_Navigation_small_navigation :: unit 
exit_Navigation_small_navigation :: unit 
\<comment> \<open>var_channel_stmbd_Navigation_small_navigation\<close>

get_target :: "nat"
set_target :: "nat"
setL_target :: "nat"
setR_target :: "nat"
get_position :: "nat"
set_position :: "nat"
setL_position :: "nat"
setR_position :: "nat"
\<comment> \<open>event_channel_stmbd_Navigation_small_navigation\<close>

proposal_in :: "nat"
proposal_out :: "nat"
setTarget_in :: "nat"
setTarget_out :: "nat"
targetReached_in :: unit 
targetReached_out :: unit 
globalpose_in :: "nat"
globalpose_out :: "nat"
OAApplied_in :: unit 
OAApplied_out :: unit 
proposal__in :: "NIDS_Navigation_small_navigation\<times>nat"
setTarget__in :: "NIDS_Navigation_small_navigation\<times>nat"
targetReached__in :: "NIDS_Navigation_small_navigation"
globalpose__in :: "NIDS_Navigation_small_navigation\<times>nat"
OAApplied__in :: "NIDS_Navigation_small_navigation"
\<comment> \<open>junction_channel_in_stmbd_i0_Navigation_small_navigation\<close>

enter_i0_Navigation_small_navigation :: unit 
interrupt_i0_Navigation_small_navigation :: unit 
\<comment> \<open>state_channel_in_stmbd_WaitTarget_Navigation_small_navigation\<close>

enter_WaitTarget_Navigation_small_navigation :: unit 
entered_WaitTarget_Navigation_small_navigation :: unit 
interrupt_WaitTarget_Navigation_small_navigation :: unit 
enteredL_WaitTarget_Navigation_small_navigation :: unit 
enteredR_WaitTarget_Navigation_small_navigation :: unit 
\<comment> \<open>state_channel_in_stmbd_WaitForPose_Navigation_small_navigation\<close>

enter_WaitForPose_Navigation_small_navigation :: unit 
entered_WaitForPose_Navigation_small_navigation :: unit 
interrupt_WaitForPose_Navigation_small_navigation :: unit 
enteredL_WaitForPose_Navigation_small_navigation :: unit 
enteredR_WaitForPose_Navigation_small_navigation :: unit 
\<comment> \<open>junction_channel_in_stmbd_CheckPosition_Navigation_small_navigation\<close>

enter_CheckPosition_Navigation_small_navigation :: unit 
interrupt_CheckPosition_Navigation_small_navigation :: unit 
\<comment> \<open>state_channel_in_stmbd_WaitMoveApplied_Navigation_small_navigation\<close>

enter_WaitMoveApplied_Navigation_small_navigation :: unit 
entered_WaitMoveApplied_Navigation_small_navigation :: unit 
interrupt_WaitMoveApplied_Navigation_small_navigation :: unit 
enteredL_WaitMoveApplied_Navigation_small_navigation :: unit 
enteredR_WaitMoveApplied_Navigation_small_navigation :: unit 
\<comment> \<open>state_channel_in_stmbd_WaitStopApplied_Navigation_small_navigation\<close>

enter_WaitStopApplied_Navigation_small_navigation :: unit 
entered_WaitStopApplied_Navigation_small_navigation :: unit 
interrupt_WaitStopApplied_Navigation_small_navigation :: unit 
enteredL_WaitStopApplied_Navigation_small_navigation :: unit 
enteredR_WaitStopApplied_Navigation_small_navigation :: unit 
\<comment> \<open>state_channel_in_stmbd_f0_Navigation_small_navigation\<close>

enter_f0_Navigation_small_navigation :: unit 
entered_f0_Navigation_small_navigation :: unit 
interrupt_f0_Navigation_small_navigation :: unit 
enteredL_f0_Navigation_small_navigation :: unit 
enteredR_f0_Navigation_small_navigation :: unit 
\<comment> \<open>assumption-guarantee_viol_Navigation_small_navigation\<close>

aviol :: unit 
gviol :: unit

(* namespace to avoid conflict with mutant/original robochart model *)
setup \<open>Sign.add_path "Navigation"\<close>

\<comment> \<open>ChannelSet Decleration\<close>
	
definition "enterSS_in_stmbd_Navigation_small_navigation = \<lbrace> 
	  enter_i0_Navigation_small_navigation, 
	  enter_WaitTarget_Navigation_small_navigation, 
	  enter_WaitForPose_Navigation_small_navigation, 
	  enter_CheckPosition_Navigation_small_navigation, 
	  enter_WaitMoveApplied_Navigation_small_navigation, 
	  enter_WaitStopApplied_Navigation_small_navigation, 
	  enter_f0_Navigation_small_navigation \<rbrace>"
	
definition "enteredSS_in_stmbd_Navigation_small_navigation = \<lbrace> 
	  entered_WaitForPose_Navigation_small_navigation, 
	  entered_WaitMoveApplied_Navigation_small_navigation, 
	  entered_WaitTarget_Navigation_small_navigation, 
	  entered_WaitStopApplied_Navigation_small_navigation, 
	  entered_f0_Navigation_small_navigation \<rbrace>"
	
definition "internal_events_in_stmbd_Navigation_small_navigation = \<lbrace> 
	  enter_i0_Navigation_small_navigation, 
	  enter_WaitTarget_Navigation_small_navigation, 
	  enter_WaitForPose_Navigation_small_navigation, 
	  enter_CheckPosition_Navigation_small_navigation, 
	  enter_WaitMoveApplied_Navigation_small_navigation, 
	  enter_WaitStopApplied_Navigation_small_navigation, 
	  enter_f0_Navigation_small_navigation, 
	  entered_WaitForPose_Navigation_small_navigation, 
	  entered_WaitMoveApplied_Navigation_small_navigation, 
	  entered_WaitTarget_Navigation_small_navigation, 
	  entered_WaitStopApplied_Navigation_small_navigation, 
	  entered_f0_Navigation_small_navigation, 
	  interrupt_Navigation_small_navigation, 
	  exited_Navigation_small_navigation \<rbrace>"
	
(* Changed the empty channel set \<lbrace> \<rbrace> to ({} :: mychan set) because Isabelle cannot parse the generated form. *)
definition "shared_variable_events_in_stmbd_Navigation_small_navigation = ({} :: mychan set)"
	
definition "sem__events_stm_Navigation_small_navigation = \<lbrace> 
	  terminate \<rbrace>"

definition relu :: "real \<Rightarrow> real" where
		   "relu x = max 0 x"

definition norm :: "real \<Rightarrow> (real \<times> real) \<Rightarrow> (real \<times> real) \<Rightarrow> real" where
		   "norm x r r' = (((x - fst(r)) / (snd(r) - fst(r))) 
                              * (snd(r') - fst(r'))) + fst(r')"
                              

abbreviation "assume b Q P \<equiv> (if b then P else aviol \<rightarrow> Q)"
(* Changed STOP to Stop because STOP could not be found in the imported library. *)
abbreviation "guar b P \<equiv> (if b then P else gviol \<rightarrow> Stop)"



(* Added project_triggers because the generated renaming leaves x unbound, which Isabelle rejects. *)
definition project_triggers :: "(mychan \<times> mychan) set" where
  "project_triggers = {(build\<^bsub>globalpose__in\<^esub> (n,v), build\<^bsub>globalpose_in\<^esub> v) |n v. True} \<union>
    {(build\<^bsub>OAApplied__in\<^esub> n, build\<^bsub>OAApplied_in\<^esub> ()) |n. True} \<union>
    {(build\<^bsub>setTarget__in\<^esub> (n,v), build\<^bsub>setTarget_in\<^esub> v) |n v. True}"

(* Changed the action type from action to cyphyaction and added the | between equations. *)
actions  is "(mychan, unit) cyphyaction" where
"SSTOP = share  \<rightarrow>  SSTOP" |
" InactiveJct_i0_Navigation_small_navigation = 	(SSTOP \<triangle> (Activation_i0_Navigation_small_navigation
                                               	  \<box>
                                               	  Termination_i0_Navigation_small_navigation)) " |

" Activation_i0_Navigation_small_navigation = 	(enter_i0_Navigation_small_navigation \<rightarrow> Active_i0_Navigation_small_navigation) " |

" Termination_i0_Navigation_small_navigation = 	(terminate \<rightarrow> Skip) " |

" Active_i0_Navigation_small_navigation = 	((SSTOP \<triangle> (interrupt_i0_Navigation_small_navigation \<rightarrow> Skip));; InactiveJct_i0_Navigation_small_navigation) " |

" Inactive_WaitTarget_Navigation_small_navigation = 	(SSTOP \<triangle> (Activation_WaitTarget_Navigation_small_navigation
                                                    	  \<box>
                                                    	  Termination_WaitTarget_Navigation_small_navigation)) " |

" Activation_WaitTarget_Navigation_small_navigation = 	(enter_WaitTarget_Navigation_small_navigation \<rightarrow> Active_WaitTarget_Navigation_small_navigation) " |

" Termination_WaitTarget_Navigation_small_navigation = 	(terminate \<rightarrow> Skip) " |

" Active_WaitTarget_Navigation_small_navigation = 	(Skip;; (Behaviour_WaitTarget_Navigation_small_navigation;; Exiting_WaitTarget_Navigation_small_navigation)) " |

" Behaviour_WaitTarget_Navigation_small_navigation = 	(entered_WaitTarget_Navigation_small_navigation \<rightarrow> During_WaitTarget_Navigation_small_navigation) " |

" During_WaitTarget_Navigation_small_navigation = 	((Skip;; SSTOP) \<triangle> (interrupt_WaitTarget_Navigation_small_navigation \<rightarrow> Skip)) " |

" Exiting_WaitTarget_Navigation_small_navigation = 	((SSTOP \<triangle> (exit_Navigation_small_navigation \<rightarrow> Skip));; (Skip;; (exited_Navigation_small_navigation \<rightarrow> Inactive_WaitTarget_Navigation_small_navigation))) " |

" Inactive_WaitForPose_Navigation_small_navigation = 	(SSTOP \<triangle> (Activation_WaitForPose_Navigation_small_navigation
                                                     	  \<box>
                                                     	  Termination_WaitForPose_Navigation_small_navigation)) " |

" Activation_WaitForPose_Navigation_small_navigation = 	(enter_WaitForPose_Navigation_small_navigation \<rightarrow> Active_WaitForPose_Navigation_small_navigation) " |

" Termination_WaitForPose_Navigation_small_navigation = 	(terminate \<rightarrow> Skip) " |

" Active_WaitForPose_Navigation_small_navigation = 	(Skip;; (Behaviour_WaitForPose_Navigation_small_navigation;; Exiting_WaitForPose_Navigation_small_navigation)) " |

" Behaviour_WaitForPose_Navigation_small_navigation = 	(entered_WaitForPose_Navigation_small_navigation \<rightarrow> During_WaitForPose_Navigation_small_navigation) " |

" During_WaitForPose_Navigation_small_navigation = 	((Skip;; SSTOP) \<triangle> (interrupt_WaitForPose_Navigation_small_navigation \<rightarrow> Skip)) " |

" Exiting_WaitForPose_Navigation_small_navigation = 	((SSTOP \<triangle> (exit_Navigation_small_navigation \<rightarrow> Skip));; (Skip;; (exited_Navigation_small_navigation \<rightarrow> Inactive_WaitForPose_Navigation_small_navigation))) " |

" InactiveJct_CheckPosition_Navigation_small_navigation = 	(SSTOP \<triangle> (Activation_CheckPosition_Navigation_small_navigation
                                                          	  \<box>
                                                          	  Termination_CheckPosition_Navigation_small_navigation)) " |

" Activation_CheckPosition_Navigation_small_navigation = 	(enter_CheckPosition_Navigation_small_navigation \<rightarrow> Active_CheckPosition_Navigation_small_navigation) " |

" Termination_CheckPosition_Navigation_small_navigation = 	(terminate \<rightarrow> Skip) " |

" Active_CheckPosition_Navigation_small_navigation = 	((SSTOP \<triangle> (interrupt_CheckPosition_Navigation_small_navigation \<rightarrow> Skip));; InactiveJct_CheckPosition_Navigation_small_navigation) " |

" Inactive_WaitMoveApplied_Navigation_small_navigation = 	(SSTOP \<triangle> (Activation_WaitMoveApplied_Navigation_small_navigation
                                                         	  \<box>
                                                         	  Termination_WaitMoveApplied_Navigation_small_navigation)) " |

" Activation_WaitMoveApplied_Navigation_small_navigation = 	(enter_WaitMoveApplied_Navigation_small_navigation \<rightarrow> Active_WaitMoveApplied_Navigation_small_navigation) " |

" Termination_WaitMoveApplied_Navigation_small_navigation = 	(terminate \<rightarrow> Skip) " |

" Active_WaitMoveApplied_Navigation_small_navigation = 	(Skip;; (Behaviour_WaitMoveApplied_Navigation_small_navigation;; Exiting_WaitMoveApplied_Navigation_small_navigation)) " |

" Behaviour_WaitMoveApplied_Navigation_small_navigation = 	(entered_WaitMoveApplied_Navigation_small_navigation \<rightarrow> During_WaitMoveApplied_Navigation_small_navigation) " |

" During_WaitMoveApplied_Navigation_small_navigation = 	((Skip;; SSTOP) \<triangle> (interrupt_WaitMoveApplied_Navigation_small_navigation \<rightarrow> Skip)) " |

" Exiting_WaitMoveApplied_Navigation_small_navigation = 	((SSTOP \<triangle> (exit_Navigation_small_navigation \<rightarrow> Skip));; (Skip;; (exited_Navigation_small_navigation \<rightarrow> Inactive_WaitMoveApplied_Navigation_small_navigation))) " |

" Inactive_WaitStopApplied_Navigation_small_navigation = 	(SSTOP \<triangle> (Activation_WaitStopApplied_Navigation_small_navigation
                                                         	  \<box>
                                                         	  Termination_WaitStopApplied_Navigation_small_navigation)) " |

" Activation_WaitStopApplied_Navigation_small_navigation = 	(enter_WaitStopApplied_Navigation_small_navigation \<rightarrow> Active_WaitStopApplied_Navigation_small_navigation) " |

" Termination_WaitStopApplied_Navigation_small_navigation = 	(terminate \<rightarrow> Skip) " |

" Active_WaitStopApplied_Navigation_small_navigation = 	(Skip;; (Behaviour_WaitStopApplied_Navigation_small_navigation;; Exiting_WaitStopApplied_Navigation_small_navigation)) " |

" Behaviour_WaitStopApplied_Navigation_small_navigation = 	(entered_WaitStopApplied_Navigation_small_navigation \<rightarrow> During_WaitStopApplied_Navigation_small_navigation) " |

" During_WaitStopApplied_Navigation_small_navigation = 	((Skip;; SSTOP) \<triangle> (interrupt_WaitStopApplied_Navigation_small_navigation \<rightarrow> Skip)) " |

" Exiting_WaitStopApplied_Navigation_small_navigation = 	((SSTOP \<triangle> (exit_Navigation_small_navigation \<rightarrow> Skip));; (Skip;; (exited_Navigation_small_navigation \<rightarrow> Inactive_WaitStopApplied_Navigation_small_navigation))) " |

" InactiveFn_f0_Navigation_small_navigation = 	(SSTOP \<triangle> (Activation_f0_Navigation_small_navigation
                                              	  \<box>
                                              	  Termination_f0_Navigation_small_navigation)) " |

" Activation_f0_Navigation_small_navigation = 	(enter_f0_Navigation_small_navigation \<rightarrow> Entering_f0_Navigation_small_navigation) " |

" Termination_f0_Navigation_small_navigation = 	(terminate \<rightarrow> Skip) " |

" Entering_f0_Navigation_small_navigation = 	(entered_f0_Navigation_small_navigation \<rightarrow> Active_f0_Navigation_small_navigation) " |

" Active_f0_Navigation_small_navigation = 	(SSTOP \<triangle> (Termination_f0_Navigation_small_navigation
                                          	  \<box>
                                          	  (interrupt_f0_Navigation_small_navigation \<rightarrow> Interrupted_f0_Navigation_small_navigation))) " |

" Interrupted_f0_Navigation_small_navigation = 	(SSTOP \<triangle> (exit_Navigation_small_navigation \<rightarrow> (exited_Navigation_small_navigation \<rightarrow> InactiveFn_f0_Navigation_small_navigation))) " |

(* Changed \<lbrakk> | cs | \<rbrakk> to \<lbrakk> \<^bold>0 | cs | \<^bold>0 \<rbrakk>, here and below, because Isabelle cannot parse the omitted name sets. *)
" composeNodes_Navigation_small_navigation = 	((((((InactiveFn_f0_Navigation_small_navigation
                                             	  \<lbrakk> \<^bold>0 | \<lbrace> share,terminate \<rbrace> | \<^bold>0 \<rbrakk> 
                                             	  Inactive_WaitMoveApplied_Navigation_small_navigation)
                                             	  \<lbrakk> \<^bold>0 | \<lbrace> share,terminate \<rbrace> | \<^bold>0 \<rbrakk> 
                                             	  Inactive_WaitStopApplied_Navigation_small_navigation)
                                             	  \<lbrakk> \<^bold>0 | \<lbrace> share,terminate \<rbrace> | \<^bold>0 \<rbrakk> 
                                             	  Inactive_WaitForPose_Navigation_small_navigation)
                                             	  \<lbrakk> \<^bold>0 | \<lbrace> share,terminate \<rbrace> | \<^bold>0 \<rbrakk> 
                                             	  InactiveJct_i0_Navigation_small_navigation)
                                             	  \<lbrakk> \<^bold>0 | \<lbrace> share,terminate \<rbrace> | \<^bold>0 \<rbrakk> 
                                             	  InactiveJct_CheckPosition_Navigation_small_navigation)
                                             	  \<lbrakk> \<^bold>0 | \<lbrace> share,terminate \<rbrace> | \<^bold>0 \<rbrakk> 
                                             	  Inactive_WaitTarget_Navigation_small_navigation) " |

" Trans_Navigation_small_navigation(n) = 	((SSTOP \<triangle> (get_position\<^bold>?position \<rightarrow> (get_target\<^bold>?target \<rightarrow> (assume True (Trans_Navigation_small_navigation(n)) ((((((((((n = NID_i0_Navigation_small_navigation) \<^bold>& (((internal__Navigation_small_navigation\<^bold>.NID_i0_Navigation_small_navigation \<rightarrow> Skip);; (enter_WaitTarget_Navigation_small_navigation \<rightarrow> Trans_Navigation_small_navigation(NID_WaitTarget_Navigation_small_navigation)))))
                                         	  \<box>
                                         	  ((n = NID_WaitTarget_Navigation_small_navigation) \<^bold>& (((setTarget__in\<^bold>.NID_WaitTarget_Navigation_small_navigation\<^bold>?target \<rightarrow> (SSTOP \<triangle> (set_target\<^bold>!target \<rightarrow> Skip)));; ((SSTOP \<triangle> (exit_Navigation_small_navigation \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_Navigation_small_navigation \<rightarrow> Skip);; (enter_WaitForPose_Navigation_small_navigation \<rightarrow> Trans_Navigation_small_navigation(NID_WaitForPose_Navigation_small_navigation)))))))))
                                         	  \<box>
                                         	  ((n = NID_WaitForPose_Navigation_small_navigation) \<^bold>& (((globalpose__in\<^bold>.NID_WaitForPose_Navigation_small_navigation\<^bold>?position \<rightarrow> (SSTOP \<triangle> (set_position\<^bold>!position \<rightarrow> Skip)));; ((SSTOP \<triangle> (exit_Navigation_small_navigation \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_Navigation_small_navigation \<rightarrow> Skip);; (enter_CheckPosition_Navigation_small_navigation \<rightarrow> Trans_Navigation_small_navigation(NID_CheckPosition_Navigation_small_navigation)))))))))
                                         	  \<box>
                                         	  ((n = NID_CheckPosition_Navigation_small_navigation) \<^bold>& ((((position < target)) \<^bold>& (((internal__Navigation_small_navigation\<^bold>.NID_CheckPosition_Navigation_small_navigation \<rightarrow> (SSTOP \<triangle> (proposal_out\<^bold>!1 \<rightarrow> Skip)));; (enter_WaitMoveApplied_Navigation_small_navigation \<rightarrow> Trans_Navigation_small_navigation(NID_WaitMoveApplied_Navigation_small_navigation))))))))
                                         	  \<box>
                                         	  ((n = NID_CheckPosition_Navigation_small_navigation) \<^bold>& ((((position \<ge> target)) \<^bold>& (((internal__Navigation_small_navigation\<^bold>.NID_CheckPosition_Navigation_small_navigation \<rightarrow> (SSTOP \<triangle> (proposal_out\<^bold>!0 \<rightarrow> Skip)));; (enter_WaitStopApplied_Navigation_small_navigation \<rightarrow> Trans_Navigation_small_navigation(NID_WaitStopApplied_Navigation_small_navigation))))))))
                                         	  \<box>
                                         	  ((n = NID_WaitMoveApplied_Navigation_small_navigation) \<^bold>& (((OAApplied__in\<^bold>.NID_WaitMoveApplied_Navigation_small_navigation \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_Navigation_small_navigation \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_Navigation_small_navigation \<rightarrow> Skip);; (enter_WaitForPose_Navigation_small_navigation \<rightarrow> Trans_Navigation_small_navigation(NID_WaitForPose_Navigation_small_navigation)))))))))
                                         	  \<box>
                                         	  ((n = NID_WaitStopApplied_Navigation_small_navigation) \<^bold>& (((OAApplied__in\<^bold>.NID_WaitStopApplied_Navigation_small_navigation \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_Navigation_small_navigation \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_Navigation_small_navigation \<rightarrow> (SSTOP \<triangle> (targetReached_out \<rightarrow> Skip)));; (enter_f0_Navigation_small_navigation \<rightarrow> Trans_Navigation_small_navigation(NID_f0_Navigation_small_navigation)))))))))
                                         	  \<box>
                                         	  (share \<rightarrow> Trans_Navigation_small_navigation(n)))
                                         	  \<box>
                                         	  (((interrupt_Navigation_small_navigation \<rightarrow> (SSTOP \<triangle> (exit_Navigation_small_navigation \<rightarrow> Skip)));; (SSTOP \<triangle> (exited_Navigation_small_navigation \<rightarrow> (terminate \<rightarrow> Skip))))
                                         	  \<box>
                                         	  (terminate \<rightarrow> Skip)))))))) " |

" Transc_Navigation_small_navigation(n) = 	((SSTOP \<triangle> (get_position\<^bold>?position \<rightarrow> (get_target\<^bold>?target \<rightarrow> (assume True (Transc_Navigation_small_navigation(n)) (((((((((n = NID_i0_Navigation_small_navigation) \<^bold>& (((internal__Navigation_small_navigation\<^bold>.NID_i0_Navigation_small_navigation \<rightarrow> Skip);; (enter_WaitTarget_Navigation_small_navigation \<rightarrow> Transc_Navigation_small_navigation(NID_WaitTarget_Navigation_small_navigation)))))
                                          	  \<box>
                                          	  ((n = NID_WaitTarget_Navigation_small_navigation) \<^bold>& (((setTarget__in\<^bold>.NID_WaitTarget_Navigation_small_navigation\<^bold>?target \<rightarrow> (SSTOP \<triangle> (set_target\<^bold>!target \<rightarrow> Skip)));; ((SSTOP \<triangle> (exit_Navigation_small_navigation \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_Navigation_small_navigation \<rightarrow> Skip);; (enter_WaitForPose_Navigation_small_navigation \<rightarrow> Transc_Navigation_small_navigation(NID_WaitForPose_Navigation_small_navigation)))))))))
                                          	  \<box>
                                          	  ((n = NID_WaitForPose_Navigation_small_navigation) \<^bold>& (((globalpose__in\<^bold>.NID_WaitForPose_Navigation_small_navigation\<^bold>?position \<rightarrow> (SSTOP \<triangle> (set_position\<^bold>!position \<rightarrow> Skip)));; ((SSTOP \<triangle> (exit_Navigation_small_navigation \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_Navigation_small_navigation \<rightarrow> Skip);; (enter_CheckPosition_Navigation_small_navigation \<rightarrow> Transc_Navigation_small_navigation(NID_CheckPosition_Navigation_small_navigation)))))))))
                                          	  \<box>
                                          	  ((n = NID_CheckPosition_Navigation_small_navigation) \<^bold>& ((((position < target)) \<^bold>& (((internal__Navigation_small_navigation\<^bold>.NID_CheckPosition_Navigation_small_navigation \<rightarrow> (SSTOP \<triangle> (proposal_out\<^bold>!1 \<rightarrow> Skip)));; (enter_WaitMoveApplied_Navigation_small_navigation \<rightarrow> Transc_Navigation_small_navigation(NID_WaitMoveApplied_Navigation_small_navigation))))))))
                                          	  \<box>
                                          	  ((n = NID_CheckPosition_Navigation_small_navigation) \<^bold>& ((((position \<ge> target)) \<^bold>& (((internal__Navigation_small_navigation\<^bold>.NID_CheckPosition_Navigation_small_navigation \<rightarrow> (SSTOP \<triangle> (proposal_out\<^bold>!0 \<rightarrow> Skip)));; (enter_WaitStopApplied_Navigation_small_navigation \<rightarrow> Transc_Navigation_small_navigation(NID_WaitStopApplied_Navigation_small_navigation))))))))
                                          	  \<box>
                                          	  ((n = NID_WaitMoveApplied_Navigation_small_navigation) \<^bold>& (((OAApplied__in\<^bold>.NID_WaitMoveApplied_Navigation_small_navigation \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_Navigation_small_navigation \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_Navigation_small_navigation \<rightarrow> Skip);; (enter_WaitForPose_Navigation_small_navigation \<rightarrow> Transc_Navigation_small_navigation(NID_WaitForPose_Navigation_small_navigation)))))))))
                                          	  \<box>
                                          	  ((n = NID_WaitStopApplied_Navigation_small_navigation) \<^bold>& (((OAApplied__in\<^bold>.NID_WaitStopApplied_Navigation_small_navigation \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_Navigation_small_navigation \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_Navigation_small_navigation \<rightarrow> (SSTOP \<triangle> (targetReached_out \<rightarrow> Skip)));; (enter_f0_Navigation_small_navigation \<rightarrow> Transc_Navigation_small_navigation(NID_f0_Navigation_small_navigation)))))))))
                                          	  \<box>
                                          	  ((n = NID_f0_Navigation_small_navigation) \<^bold>& ((terminate \<rightarrow> Skip))))))))) " |

(* Changed \<cdot> to \<^bold>. because \<cdot> could not be found in the imported library. *)
(* Changed the renamings [ a \<mapsto> b, ... ] to cRename (cCompleteRenaming ...) because Isabelle cannot parse them in an equation. *)
(* Changed Trans to Trans(NID_i0) because Trans is defined with the current node as a parameter and the generated call gives none; i0 is the initial junction. *)
" ncCoreBehaviour_Navigation_small_navigation = 	((cRename (cCompleteRenaming (csbasic (share) \<times> csbasic (share))) (cRename (cCompleteRenaming ((csbasic (interrupt_i0_Navigation_small_navigation) \<times> csbasic (internal__Navigation_small_navigation\<^bold>.NID_i0_Navigation_small_navigation)) \<union> (csbasic (interrupt_WaitTarget_Navigation_small_navigation) \<times> csbasic (setTarget__in\<^bold>.NID_WaitTarget_Navigation_small_navigation)) \<union> (csbasic (interrupt_WaitForPose_Navigation_small_navigation) \<times> csbasic (globalpose__in\<^bold>.NID_WaitForPose_Navigation_small_navigation)) \<union> (csbasic (interrupt_CheckPosition_Navigation_small_navigation) \<times> csbasic (internal__Navigation_small_navigation\<^bold>.NID_CheckPosition_Navigation_small_navigation)) \<union> (csbasic (interrupt_CheckPosition_Navigation_small_navigation) \<times> csbasic (internal__Navigation_small_navigation\<^bold>.NID_CheckPosition_Navigation_small_navigation)) \<union> (csbasic (interrupt_WaitMoveApplied_Navigation_small_navigation) \<times> csbasic (OAApplied__in\<^bold>.NID_WaitMoveApplied_Navigation_small_navigation)) \<union> (csbasic (interrupt_WaitStopApplied_Navigation_small_navigation) \<times> csbasic (OAApplied__in\<^bold>.NID_WaitStopApplied_Navigation_small_navigation)) \<union> (csbasic (interrupt_WaitForPose_Navigation_small_navigation) \<times> csbasic (interrupt_Navigation_small_navigation)) \<union> (csbasic (interrupt_WaitMoveApplied_Navigation_small_navigation) \<times> csbasic (interrupt_Navigation_small_navigation)) \<union> (csbasic (interrupt_WaitTarget_Navigation_small_navigation) \<times> csbasic (interrupt_Navigation_small_navigation)) \<union> (csbasic (interrupt_WaitStopApplied_Navigation_small_navigation) \<times> csbasic (interrupt_Navigation_small_navigation)) \<union> (csbasic (interrupt_f0_Navigation_small_navigation) \<times> csbasic (interrupt_Navigation_small_navigation)))) (composeNodes_Navigation_small_navigation))) \<lbrakk> \<^bold>0 | \<lbrace> globalpose__in\<^bold>.NID_WaitForPose_Navigation_small_navigation,exit_Navigation_small_navigation,internal__Navigation_small_navigation\<^bold>.NID_CheckPosition_Navigation_small_navigation,OAApplied__in\<^bold>.NID_WaitStopApplied_Navigation_small_navigation,enter_WaitForPose_Navigation_small_navigation,enter_f0_Navigation_small_navigation,interrupt_Navigation_small_navigation,enter_i0_Navigation_small_navigation,enter_WaitStopApplied_Navigation_small_navigation,OAApplied__in\<^bold>.NID_WaitMoveApplied_Navigation_small_navigation,setTarget__in\<^bold>.NID_WaitTarget_Navigation_small_navigation,share,internal__Navigation_small_navigation\<^bold>.NID_i0_Navigation_small_navigation,terminate,enter_WaitMoveApplied_Navigation_small_navigation,exited_Navigation_small_navigation,enter_WaitTarget_Navigation_small_navigation,enter_CheckPosition_Navigation_small_navigation \<rbrace> | \<^bold>0 \<rbrakk> (cRename (cCompleteRenaming (csbasic (share) \<times> csbasic (share))) (enter_i0_Navigation_small_navigation \<rightarrow> Trans_Navigation_small_navigation(NID_i0_Navigation_small_navigation)))) " |

(* Changed the generated renaming to cRename (cCompleteRenaming project_triggers). *)
" ncBehaviour_Navigation_small_navigation = cRename (cCompleteRenaming project_triggers) (ncCoreBehaviour_Navigation_small_navigation \<Zhide> \<lbrace> enter_i0_Navigation_small_navigation,enter_WaitTarget_Navigation_small_navigation,enter_WaitForPose_Navigation_small_navigation,enter_CheckPosition_Navigation_small_navigation,enter_WaitMoveApplied_Navigation_small_navigation,enter_WaitStopApplied_Navigation_small_navigation,enter_f0_Navigation_small_navigation,exit_Navigation_small_navigation,exited_Navigation_small_navigation,internal__Navigation_small_navigation \<rbrace>) " |

(* Changed \<Zhide> \<lbrace> enteredSS_Navigation_small_navigation \<rbrace> to \<Zhide> enteredSS_in_stmbd_Navigation_small_navigation because only the second name is declared, and it is already a channel set. *)
" machineBody_Navigation_small_navigation = 	((ncBehaviour_Navigation_small_navigation
                                            	  \<lbrakk> \<^bold>0 | \<lbrace> interrupt_Navigation_small_navigation \<rbrace> | \<^bold>0 \<rbrakk> 
                                            	  Skip) \<Zhide> enteredSS_in_stmbd_Navigation_small_navigation) " |

(* Changed get_target_Navigation_small_navigation and set_target_Navigation_small_navigation to get_target and set_target because only the short names are declared, and they are what Trans and stateful use; likewise for position. *)
" Memory_target_Navigation_small_navigation(value) = 	(((get_target\<^bold>!value \<rightarrow> Memory_target_Navigation_small_navigation(value))
                                                     	  \<box>
                                                     	  ((set_target\<^bold>?x__v \<rightarrow> Memory_target_Navigation_small_navigation(x__v))
                                                     	  \<box>
                                                     	  (terminate \<rightarrow> Skip)))) " |

" Memory_position_Navigation_small_navigation(value) = 	(((get_position\<^bold>!value \<rightarrow> Memory_position_Navigation_small_navigation(value))
                                                       	  \<box>
                                                       	  ((set_position\<^bold>?x__v \<rightarrow> Memory_position_Navigation_small_navigation(x__v))
                                                       	  \<box>
                                                       	  (terminate \<rightarrow> Skip)))) " |

(* Changed (0) to (0::nat) because each equation is type-checked on its own; without the type, Memory_target and Memory_position here are not matched to their definitions. *)
" varMemory_Navigation_small_navigation = 	(Memory_target_Navigation_small_navigation(0::nat)
                                          	  \<lbrakk> \<^bold>0 | \<lbrace> terminate \<rbrace> | \<^bold>0 \<rbrakk> 
                                          	  Memory_position_Navigation_small_navigation(0::nat)) " |

" stateful_Navigation_small_navigation = 	((machineBody_Navigation_small_navigation
                                         	  \<lbrakk> \<^bold>0 | \<lbrace> set_position,get_position,get_target,set_target,terminate \<rbrace> | \<^bold>0 \<rbrakk> 
                                         	  varMemory_Navigation_small_navigation) \<Zhide> \<lbrace> set_position,get_position,get_target,set_target \<rbrace>) " |

" sharedVarMemory_Navigation_small_navigation = 	(terminate \<rightarrow> Skip) " |

(* Changed [ ] to cRename (cCompleteRenaming ({})), \<lbrace> shared \<rbrace> to the declared channel set, and \<lbrace> \<rbrace> to ({} :: mychan set). *)
" stm_Navigation_small_navigation = 	((((cRename (cCompleteRenaming ({})) ((stateful_Navigation_small_navigation \<Zhide> \<lbrace> terminate \<rbrace>);; (SSTOP \<triangle> (terminate \<rightarrow> Skip)))) \<lbrakk> \<^bold>0 | shared_variable_events_in_stmbd_Navigation_small_navigation | \<^bold>0 \<rbrakk> Skip) \<lbrakk> \<^bold>0 | \<lbrace> terminate \<rbrace> | \<^bold>0 \<rbrakk> sharedVarMemory_Navigation_small_navigation) \<Zhide> ({} :: mychan set)) "

(* Added Small_Navigation as the name of the whole model for convenience. *)
definition Small_Navigation :: "(mychan, unit) cyphyaction" where
  "Small_Navigation = stm_Navigation_small_navigation"

setup \<open>Sign.parent_path\<close>

end
