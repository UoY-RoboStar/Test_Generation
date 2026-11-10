theory Small_Navigation_Timed
  imports "Axiomatic_CyPhyCircus.Ax_CyPhyCircus"
begin

(* Changed the import from Axiomatic_Circus, which is not available, to Ax_CyPhyCircus. *)

subsection \<open> Prelude \<close>

(* Changed lit_vars to declare [[literal_variables]] because lit_vars could not be found in the imported library. *)
declare [[literal_variables]]
unbundle Circus_Syntax

hide_const (open) sum

subsection \<open> Model \<close>


	
	
(* Changed datatype to enumtype because code generation needs NIDS_Navigation_small_navigation to instantiate enum. *)
enumtype NIDS_Navigation_small_navigation =
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

get_target_Navigation_small_navigation :: "nat"
set_target_Navigation_small_navigation :: "nat"
setL_target_Navigation_small_navigation :: "nat"
setR_target_Navigation_small_navigation :: "nat"
get_position_Navigation_small_navigation :: "nat"
set_position_Navigation_small_navigation :: "nat"
setL_position_Navigation_small_navigation :: "nat"
setR_position_Navigation_small_navigation :: "nat"
\<comment> \<open>event_channel_stmbd_Navigation_small_navigation\<close>

setTarget_in :: "nat"
setTarget_out :: "nat"
targetReached_in :: unit 
targetReached_out :: unit 
globalpose_in :: "nat"
globalpose_out :: "nat"
OAApplied_in :: unit 
OAApplied_out :: unit 
proposal_in :: "nat"
proposal_out :: "nat"
setTarget__in :: "(NIDS_Navigation_small_navigation\<times>nat)"
targetReached__in :: "NIDS_Navigation_small_navigation"
globalpose__in :: "(NIDS_Navigation_small_navigation\<times>nat)"
OAApplied__in :: "NIDS_Navigation_small_navigation"
proposal__in :: "(NIDS_Navigation_small_navigation\<times>nat)"
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
(* Added the channels get_CLID_<state> for the timed semantics: every state other than a final state has a
   clock, the time since the state was entered, which guards read on this channel (RoboChart reference
   manual, Rules 76 and 88). *)
\<comment> \<open>state clocks\<close>

get_CLID_WaitTarget_Navigation_small_navigation :: nat
get_CLID_WaitForPose_Navigation_small_navigation :: nat
get_CLID_WaitMoveApplied_Navigation_small_navigation :: nat
get_CLID_WaitStopApplied_Navigation_small_navigation :: nat
(* Added the channel tock for the timed semantics: the event tock marks the passage of one time unit
   (FDR manual, Timed Sections). *)
\<comment> \<open>tock\<close>

tock :: unit
\<comment> \<open>assumption-guarantee_viol_Navigation_small_navigation\<close>

aviol :: unit 
gviol :: unit

(* Added for the timed semantics: in mychan, the event cTock of Ax_CyPhyCircus is the event of the channel
   tock. *)
instantiation mychan :: tock
begin
definition "cTock_mychan = build\<^bsub>tock\<^esub> ()"
instance ..
end

(* Added for the timed semantics: from here the CSP operators are the timed operators of Ax_CyPhyCircus, as
   in a timed section of FDR (FDR manual, Timed Sections), so each process below is a TimedCSPProcess of the
   reference manual, Section 4.2. Sequential composition, hiding and renaming are not affected. *)
unbundle Timed_Section

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
	  entered_f0_Navigation_small_navigation,
	  entered_WaitMoveApplied_Navigation_small_navigation, 
	  entered_WaitTarget_Navigation_small_navigation, 
	  entered_WaitForPose_Navigation_small_navigation,
	  entered_WaitStopApplied_Navigation_small_navigation \<rbrace>"
definition "internal_events_in_stmbd_Navigation_small_navigation = \<lbrace> 
	  enter_i0_Navigation_small_navigation, 
	  enter_WaitTarget_Navigation_small_navigation, 
	  enter_WaitForPose_Navigation_small_navigation, 
	  enter_CheckPosition_Navigation_small_navigation, 
	  enter_WaitMoveApplied_Navigation_small_navigation, 
	  enter_WaitStopApplied_Navigation_small_navigation, 
	  enter_f0_Navigation_small_navigation, 
	  entered_f0_Navigation_small_navigation,
	  entered_WaitMoveApplied_Navigation_small_navigation, 
	  entered_WaitTarget_Navigation_small_navigation, 
	  entered_WaitForPose_Navigation_small_navigation,
	  entered_WaitStopApplied_Navigation_small_navigation, 
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



(* Added for the timed semantics: the events on which the state clocks synchronise with the node container,
   the clock reads and the entered event of each state (reference manual, Rule 76, stateClockSync). *)
definition "stateClockSync_Navigation_small_navigation = \<lbrace>
	  get_CLID_WaitTarget_Navigation_small_navigation,
	  entered_WaitTarget_Navigation_small_navigation,
	  get_CLID_WaitForPose_Navigation_small_navigation,
	  entered_WaitForPose_Navigation_small_navigation,
	  get_CLID_WaitMoveApplied_Navigation_small_navigation,
	  entered_WaitMoveApplied_Navigation_small_navigation,
	  get_CLID_WaitStopApplied_Navigation_small_navigation,
	  entered_WaitStopApplied_Navigation_small_navigation \<rbrace>"

(* Added renameTriggerEvents because the generated renaming leaves x unbound, which Isabelle rejects. *)
definition renameTriggerEvents_Navigation_small_navigation :: "(mychan \<times> mychan) set" where
  "renameTriggerEvents_Navigation_small_navigation = \<lbrace> globalpose__in (n, v) \<mapsto> globalpose_in v | (n, v). True \<rbrace> \<union>
     \<lbrace> OAApplied__in n \<mapsto> OAApplied_in () | n. True \<rbrace> \<union>
     \<lbrace> setTarget__in (n, v) \<mapsto> setTarget_in v | (n, v). True \<rbrace>"
(* Changed the action type from action to cyphyaction and added the | between equations. *)
(* The processes follow the Ranger example (Ax_CyPhyCircus examples/Ranger_CyPhyCircus.thy): each group of
   mutually recursive processes is one recursive block, and the blocks and definitions appear in
   dependency order. *)

(* SSTOP is defined as an lfp directly, since recursive cannot unfold a block that refers to
   a process from an earlier recursive block. SSTOP_unfold restates the original equation. *)
definition SSTOP :: "(mychan, unit) cyphyaction" where
"SSTOP = (\<nu> X. share \<rightarrow> X)"

(* Changed cSync_mono to cTSync_mono for the timed semantics: the prefix is the timed prefix. *)
lemma SSTOP_unfold: "SSTOP = share  \<rightarrow>  SSTOP"
  unfolding SSTOP_def by (rule lfp_unfold, rule monoI, rule cTSync_mono, assumption)

definition Termination_i0_Navigation_small_navigation :: "(mychan, unit) cyphyaction" where
" Termination_i0_Navigation_small_navigation = 	(terminate \<rightarrow> Skip) "

recursive
  InactiveJct_i0_Navigation_small_navigation :: "(mychan, unit) cyphyaction" and
  Activation_i0_Navigation_small_navigation :: "(mychan, unit) cyphyaction" and
  Active_i0_Navigation_small_navigation :: "(mychan, unit) cyphyaction"
where
" InactiveJct_i0_Navigation_small_navigation = 	(SSTOP \<triangle> (Activation_i0_Navigation_small_navigation
                                               	  \<box>
                                               	  Termination_i0_Navigation_small_navigation)) " |

" Activation_i0_Navigation_small_navigation = 	(enter_i0_Navigation_small_navigation \<rightarrow> Active_i0_Navigation_small_navigation) " |

" Active_i0_Navigation_small_navigation = 	((SSTOP \<triangle> (interrupt_i0_Navigation_small_navigation \<rightarrow> Skip));; InactiveJct_i0_Navigation_small_navigation) "

definition Termination_WaitTarget_Navigation_small_navigation :: "(mychan, unit) cyphyaction" where
" Termination_WaitTarget_Navigation_small_navigation = 	(terminate \<rightarrow> Skip) "

definition During_WaitTarget_Navigation_small_navigation :: "(mychan, unit) cyphyaction" where
" During_WaitTarget_Navigation_small_navigation = 	((Skip;; SSTOP) \<triangle> (interrupt_WaitTarget_Navigation_small_navigation \<rightarrow> Skip)) "

definition Behaviour_WaitTarget_Navigation_small_navigation :: "(mychan, unit) cyphyaction" where
" Behaviour_WaitTarget_Navigation_small_navigation = 	(entered_WaitTarget_Navigation_small_navigation \<rightarrow> During_WaitTarget_Navigation_small_navigation) "

recursive
  Inactive_WaitTarget_Navigation_small_navigation :: "(mychan, unit) cyphyaction" and
  Activation_WaitTarget_Navigation_small_navigation :: "(mychan, unit) cyphyaction" and
  Active_WaitTarget_Navigation_small_navigation :: "(mychan, unit) cyphyaction" and
  Exiting_WaitTarget_Navigation_small_navigation :: "(mychan, unit) cyphyaction"
where
" Inactive_WaitTarget_Navigation_small_navigation = 	(SSTOP \<triangle> (Activation_WaitTarget_Navigation_small_navigation
                                                    	  \<box>
                                                    	  Termination_WaitTarget_Navigation_small_navigation)) " |

" Activation_WaitTarget_Navigation_small_navigation = 	(enter_WaitTarget_Navigation_small_navigation \<rightarrow> Active_WaitTarget_Navigation_small_navigation) " |

" Active_WaitTarget_Navigation_small_navigation = 	(Skip;; (Behaviour_WaitTarget_Navigation_small_navigation;; Exiting_WaitTarget_Navigation_small_navigation)) " |

" Exiting_WaitTarget_Navigation_small_navigation = 	((SSTOP \<triangle> (exit_Navigation_small_navigation \<rightarrow> Skip));; (Skip;; (exited_Navigation_small_navigation \<rightarrow> Inactive_WaitTarget_Navigation_small_navigation))) "

definition Termination_WaitForPose_Navigation_small_navigation :: "(mychan, unit) cyphyaction" where
" Termination_WaitForPose_Navigation_small_navigation = 	(terminate \<rightarrow> Skip) "

definition During_WaitForPose_Navigation_small_navigation :: "(mychan, unit) cyphyaction" where
" During_WaitForPose_Navigation_small_navigation = 	((Skip;; SSTOP) \<triangle> (interrupt_WaitForPose_Navigation_small_navigation \<rightarrow> Skip)) "

definition Behaviour_WaitForPose_Navigation_small_navigation :: "(mychan, unit) cyphyaction" where
" Behaviour_WaitForPose_Navigation_small_navigation = 	(entered_WaitForPose_Navigation_small_navigation \<rightarrow> During_WaitForPose_Navigation_small_navigation) "

recursive
  Inactive_WaitForPose_Navigation_small_navigation :: "(mychan, unit) cyphyaction" and
  Activation_WaitForPose_Navigation_small_navigation :: "(mychan, unit) cyphyaction" and
  Active_WaitForPose_Navigation_small_navigation :: "(mychan, unit) cyphyaction" and
  Exiting_WaitForPose_Navigation_small_navigation :: "(mychan, unit) cyphyaction"
where
" Inactive_WaitForPose_Navigation_small_navigation = 	(SSTOP \<triangle> (Activation_WaitForPose_Navigation_small_navigation
                                                     	  \<box>
                                                     	  Termination_WaitForPose_Navigation_small_navigation)) " |

" Activation_WaitForPose_Navigation_small_navigation = 	(enter_WaitForPose_Navigation_small_navigation \<rightarrow> Active_WaitForPose_Navigation_small_navigation) " |

" Active_WaitForPose_Navigation_small_navigation = 	(Skip;; (Behaviour_WaitForPose_Navigation_small_navigation;; Exiting_WaitForPose_Navigation_small_navigation)) " |

" Exiting_WaitForPose_Navigation_small_navigation = 	((SSTOP \<triangle> (exit_Navigation_small_navigation \<rightarrow> Skip));; (Skip;; (exited_Navigation_small_navigation \<rightarrow> Inactive_WaitForPose_Navigation_small_navigation))) "

definition Termination_CheckPosition_Navigation_small_navigation :: "(mychan, unit) cyphyaction" where
" Termination_CheckPosition_Navigation_small_navigation = 	(terminate \<rightarrow> Skip) "

recursive
  InactiveJct_CheckPosition_Navigation_small_navigation :: "(mychan, unit) cyphyaction" and
  Activation_CheckPosition_Navigation_small_navigation :: "(mychan, unit) cyphyaction" and
  Active_CheckPosition_Navigation_small_navigation :: "(mychan, unit) cyphyaction"
where
" InactiveJct_CheckPosition_Navigation_small_navigation = 	(SSTOP \<triangle> (Activation_CheckPosition_Navigation_small_navigation
                                                          	  \<box>
                                                          	  Termination_CheckPosition_Navigation_small_navigation)) " |

" Activation_CheckPosition_Navigation_small_navigation = 	(enter_CheckPosition_Navigation_small_navigation \<rightarrow> Active_CheckPosition_Navigation_small_navigation) " |

" Active_CheckPosition_Navigation_small_navigation = 	((SSTOP \<triangle> (interrupt_CheckPosition_Navigation_small_navigation \<rightarrow> Skip));; InactiveJct_CheckPosition_Navigation_small_navigation) "

definition Termination_WaitMoveApplied_Navigation_small_navigation :: "(mychan, unit) cyphyaction" where
" Termination_WaitMoveApplied_Navigation_small_navigation = 	(terminate \<rightarrow> Skip) "

definition During_WaitMoveApplied_Navigation_small_navigation :: "(mychan, unit) cyphyaction" where
" During_WaitMoveApplied_Navigation_small_navigation = 	((Skip;; SSTOP) \<triangle> (interrupt_WaitMoveApplied_Navigation_small_navigation \<rightarrow> Skip)) "

definition Behaviour_WaitMoveApplied_Navigation_small_navigation :: "(mychan, unit) cyphyaction" where
" Behaviour_WaitMoveApplied_Navigation_small_navigation = 	(entered_WaitMoveApplied_Navigation_small_navigation \<rightarrow> During_WaitMoveApplied_Navigation_small_navigation) "

recursive
  Inactive_WaitMoveApplied_Navigation_small_navigation :: "(mychan, unit) cyphyaction" and
  Activation_WaitMoveApplied_Navigation_small_navigation :: "(mychan, unit) cyphyaction" and
  Active_WaitMoveApplied_Navigation_small_navigation :: "(mychan, unit) cyphyaction" and
  Exiting_WaitMoveApplied_Navigation_small_navigation :: "(mychan, unit) cyphyaction"
where
" Inactive_WaitMoveApplied_Navigation_small_navigation = 	(SSTOP \<triangle> (Activation_WaitMoveApplied_Navigation_small_navigation
                                                         	  \<box>
                                                         	  Termination_WaitMoveApplied_Navigation_small_navigation)) " |

" Activation_WaitMoveApplied_Navigation_small_navigation = 	(enter_WaitMoveApplied_Navigation_small_navigation \<rightarrow> Active_WaitMoveApplied_Navigation_small_navigation) " |

" Active_WaitMoveApplied_Navigation_small_navigation = 	(Skip;; (Behaviour_WaitMoveApplied_Navigation_small_navigation;; Exiting_WaitMoveApplied_Navigation_small_navigation)) " |

" Exiting_WaitMoveApplied_Navigation_small_navigation = 	((SSTOP \<triangle> (exit_Navigation_small_navigation \<rightarrow> Skip));; (Skip;; (exited_Navigation_small_navigation \<rightarrow> Inactive_WaitMoveApplied_Navigation_small_navigation))) "

definition Termination_WaitStopApplied_Navigation_small_navigation :: "(mychan, unit) cyphyaction" where
" Termination_WaitStopApplied_Navigation_small_navigation = 	(terminate \<rightarrow> Skip) "

definition During_WaitStopApplied_Navigation_small_navigation :: "(mychan, unit) cyphyaction" where
" During_WaitStopApplied_Navigation_small_navigation = 	((Skip;; SSTOP) \<triangle> (interrupt_WaitStopApplied_Navigation_small_navigation \<rightarrow> Skip)) "

definition Behaviour_WaitStopApplied_Navigation_small_navigation :: "(mychan, unit) cyphyaction" where
" Behaviour_WaitStopApplied_Navigation_small_navigation = 	(entered_WaitStopApplied_Navigation_small_navigation \<rightarrow> During_WaitStopApplied_Navigation_small_navigation) "

recursive
  Inactive_WaitStopApplied_Navigation_small_navigation :: "(mychan, unit) cyphyaction" and
  Activation_WaitStopApplied_Navigation_small_navigation :: "(mychan, unit) cyphyaction" and
  Active_WaitStopApplied_Navigation_small_navigation :: "(mychan, unit) cyphyaction" and
  Exiting_WaitStopApplied_Navigation_small_navigation :: "(mychan, unit) cyphyaction"
where
" Inactive_WaitStopApplied_Navigation_small_navigation = 	(SSTOP \<triangle> (Activation_WaitStopApplied_Navigation_small_navigation
                                                         	  \<box>
                                                         	  Termination_WaitStopApplied_Navigation_small_navigation)) " |

" Activation_WaitStopApplied_Navigation_small_navigation = 	(enter_WaitStopApplied_Navigation_small_navigation \<rightarrow> Active_WaitStopApplied_Navigation_small_navigation) " |

" Active_WaitStopApplied_Navigation_small_navigation = 	(Skip;; (Behaviour_WaitStopApplied_Navigation_small_navigation;; Exiting_WaitStopApplied_Navigation_small_navigation)) " |

" Exiting_WaitStopApplied_Navigation_small_navigation = 	((SSTOP \<triangle> (exit_Navigation_small_navigation \<rightarrow> Skip));; (Skip;; (exited_Navigation_small_navigation \<rightarrow> Inactive_WaitStopApplied_Navigation_small_navigation))) "

definition Termination_f0_Navigation_small_navigation :: "(mychan, unit) cyphyaction" where
" Termination_f0_Navigation_small_navigation = 	(terminate \<rightarrow> Skip) "

recursive
  InactiveFn_f0_Navigation_small_navigation :: "(mychan, unit) cyphyaction" and
  Activation_f0_Navigation_small_navigation :: "(mychan, unit) cyphyaction" and
  Entering_f0_Navigation_small_navigation :: "(mychan, unit) cyphyaction" and
  Active_f0_Navigation_small_navigation :: "(mychan, unit) cyphyaction" and
  Interrupted_f0_Navigation_small_navigation :: "(mychan, unit) cyphyaction"
where
" InactiveFn_f0_Navigation_small_navigation = 	(SSTOP \<triangle> (Activation_f0_Navigation_small_navigation
                                              	  \<box>
                                              	  Termination_f0_Navigation_small_navigation)) " |

" Activation_f0_Navigation_small_navigation = 	(enter_f0_Navigation_small_navigation \<rightarrow> Entering_f0_Navigation_small_navigation) " |

" Entering_f0_Navigation_small_navigation = 	(entered_f0_Navigation_small_navigation \<rightarrow> Active_f0_Navigation_small_navigation) " |

" Active_f0_Navigation_small_navigation = 	(SSTOP \<triangle> (Termination_f0_Navigation_small_navigation
                                          	  \<box>
                                          	  (interrupt_f0_Navigation_small_navigation \<rightarrow> Interrupted_f0_Navigation_small_navigation))) " |

" Interrupted_f0_Navigation_small_navigation = 	(SSTOP \<triangle> (exit_Navigation_small_navigation \<rightarrow> (exited_Navigation_small_navigation \<rightarrow> InactiveFn_f0_Navigation_small_navigation))) "

(* Changed \<lbrakk> | cs | \<rbrakk> to \<lbrakk> \<^bold>0 | cs | \<^bold>0 \<rbrakk>, here and below, because Isabelle cannot parse the omitted name sets. *)
definition composeNodes_Navigation_small_navigation :: "(mychan, unit) cyphyaction" where
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
                                                	  Inactive_WaitTarget_Navigation_small_navigation) "

(* Changed Trans for the timed semantics (reference manual, Rule 82): the choice over the transitions and share,
   T, is cInitialTimeout1 T (Trans(n)), where the manual has (T \<triangleright>\<^sub>1 Skip); Trans, so when a time unit passes
   without a transition the variables are read again and the guards evaluated anew; the interrupt and terminate
   branches stay outside the timeout. cInitialTimeout1 P Q is P \<triangleright>\<^sub>1 Q: the first event of P resolves it, and after
   one time unit without an event it behaves as Q. The branches of T continue with Trans as in the untimed
   model, so Trans(n) follows the time unit only. Each read of a guard variable is in choice with StopU, as in
   the manual, Stop\<^sub>U \<box> get_v?x \<rightarrow> ... (Rules 90 and 91): no time passes before the read. *)
recursive
  Trans_Navigation_small_navigation :: "NIDS_Navigation_small_navigation \<Rightarrow> (mychan, unit) cyphyaction"
where
" Trans_Navigation_small_navigation(n) = 	((SSTOP \<triangle> (StopU \<box> (get_position_Navigation_small_navigation\<^bold>?position_Navigation_small_navigation \<rightarrow> (StopU \<box> (get_target_Navigation_small_navigation\<^bold>?target_Navigation_small_navigation \<rightarrow> (assume True (Trans_Navigation_small_navigation(n)) ((cInitialTimeout1 (((((((((n = NID_i0_Navigation_small_navigation) \<^bold>& (((internal__Navigation_small_navigation\<^bold>.NID_i0_Navigation_small_navigation \<rightarrow> Skip);; (enter_WaitTarget_Navigation_small_navigation \<rightarrow> Trans_Navigation_small_navigation(NID_WaitTarget_Navigation_small_navigation)))))
                                         	  \<box>
                                         	  ((n = NID_WaitTarget_Navigation_small_navigation) \<^bold>& (((setTarget__in\<^bold>.NID_WaitTarget_Navigation_small_navigation\<^bold>?target_Navigation_small_navigation \<rightarrow> (SSTOP \<triangle> (set_target_Navigation_small_navigation\<^bold>!target_Navigation_small_navigation \<rightarrow> Skip)));; ((SSTOP \<triangle> (exit_Navigation_small_navigation \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_Navigation_small_navigation \<rightarrow> Skip);; (enter_WaitForPose_Navigation_small_navigation \<rightarrow> Trans_Navigation_small_navigation(NID_WaitForPose_Navigation_small_navigation)))))))))
                                         	  \<box>
                                         	  ((n = NID_WaitForPose_Navigation_small_navigation) \<^bold>& (((globalpose__in\<^bold>.NID_WaitForPose_Navigation_small_navigation\<^bold>?position_Navigation_small_navigation \<rightarrow> (SSTOP \<triangle> (set_position_Navigation_small_navigation\<^bold>!position_Navigation_small_navigation \<rightarrow> Skip)));; ((SSTOP \<triangle> (exit_Navigation_small_navigation \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_Navigation_small_navigation \<rightarrow> Skip);; (enter_CheckPosition_Navigation_small_navigation \<rightarrow> Trans_Navigation_small_navigation(NID_CheckPosition_Navigation_small_navigation)))))))))
                                         	  \<box>
                                         	  ((n = NID_CheckPosition_Navigation_small_navigation) \<^bold>& ((((position_Navigation_small_navigation < target_Navigation_small_navigation)) \<^bold>& (((internal__Navigation_small_navigation\<^bold>.NID_CheckPosition_Navigation_small_navigation \<rightarrow> (SSTOP \<triangle> (proposal_out\<^bold>!1 \<rightarrow> Skip)));; (enter_WaitMoveApplied_Navigation_small_navigation \<rightarrow> Trans_Navigation_small_navigation(NID_WaitMoveApplied_Navigation_small_navigation))))))))
                                         	  \<box>
                                         	  ((n = NID_CheckPosition_Navigation_small_navigation) \<^bold>& ((((position_Navigation_small_navigation \<ge> target_Navigation_small_navigation)) \<^bold>& (((internal__Navigation_small_navigation\<^bold>.NID_CheckPosition_Navigation_small_navigation \<rightarrow> (SSTOP \<triangle> (proposal_out\<^bold>!0 \<rightarrow> Skip)));; (enter_WaitStopApplied_Navigation_small_navigation \<rightarrow> Trans_Navigation_small_navigation(NID_WaitStopApplied_Navigation_small_navigation))))))))
                                         	  \<box>
                                         	  ((n = NID_WaitMoveApplied_Navigation_small_navigation) \<^bold>& (((OAApplied__in\<^bold>.NID_WaitMoveApplied_Navigation_small_navigation \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_Navigation_small_navigation \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_Navigation_small_navigation \<rightarrow> Skip);; (enter_WaitForPose_Navigation_small_navigation \<rightarrow> Trans_Navigation_small_navigation(NID_WaitForPose_Navigation_small_navigation)))))))))
                                         	  \<box>
                                         	  ((n = NID_WaitStopApplied_Navigation_small_navigation) \<^bold>& (((OAApplied__in\<^bold>.NID_WaitStopApplied_Navigation_small_navigation \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_Navigation_small_navigation \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_Navigation_small_navigation \<rightarrow> (SSTOP \<triangle> (targetReached_out \<rightarrow> Skip)));; (enter_f0_Navigation_small_navigation \<rightarrow> Trans_Navigation_small_navigation(NID_f0_Navigation_small_navigation)))))))))
                                         	  \<box>
                                         	  (share \<rightarrow> Trans_Navigation_small_navigation(n))) (Trans_Navigation_small_navigation(n)))
                                         	  \<box>
                                         	  (((interrupt_Navigation_small_navigation \<rightarrow> (SSTOP \<triangle> (exit_Navigation_small_navigation \<rightarrow> Skip)));; (SSTOP \<triangle> (exited_Navigation_small_navigation \<rightarrow> (terminate \<rightarrow> Skip))))
                                         	  \<box>
                                            	  (terminate \<rightarrow> Skip)))))))))) "

recursive
  Transc_Navigation_small_navigation :: "NIDS_Navigation_small_navigation \<Rightarrow> (mychan, unit) cyphyaction"
where
" Transc_Navigation_small_navigation(n) = 	((SSTOP \<triangle> (get_position_Navigation_small_navigation\<^bold>?position_Navigation_small_navigation \<rightarrow> (get_target_Navigation_small_navigation\<^bold>?target_Navigation_small_navigation \<rightarrow> (assume True (Transc_Navigation_small_navigation(n)) (((((((((n = NID_i0_Navigation_small_navigation) \<^bold>& (((internal__Navigation_small_navigation\<^bold>.NID_i0_Navigation_small_navigation \<rightarrow> Skip);; (enter_WaitTarget_Navigation_small_navigation \<rightarrow> Transc_Navigation_small_navigation(NID_WaitTarget_Navigation_small_navigation)))))
                                          	  \<box>
                                          	  ((n = NID_WaitTarget_Navigation_small_navigation) \<^bold>& (((setTarget__in\<^bold>.NID_WaitTarget_Navigation_small_navigation\<^bold>?target_Navigation_small_navigation \<rightarrow> (SSTOP \<triangle> (set_target_Navigation_small_navigation\<^bold>!target_Navigation_small_navigation \<rightarrow> Skip)));; ((SSTOP \<triangle> (exit_Navigation_small_navigation \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_Navigation_small_navigation \<rightarrow> Skip);; (enter_WaitForPose_Navigation_small_navigation \<rightarrow> Transc_Navigation_small_navigation(NID_WaitForPose_Navigation_small_navigation)))))))))
                                          	  \<box>
                                          	  ((n = NID_WaitForPose_Navigation_small_navigation) \<^bold>& (((globalpose__in\<^bold>.NID_WaitForPose_Navigation_small_navigation\<^bold>?position_Navigation_small_navigation \<rightarrow> (SSTOP \<triangle> (set_position_Navigation_small_navigation\<^bold>!position_Navigation_small_navigation \<rightarrow> Skip)));; ((SSTOP \<triangle> (exit_Navigation_small_navigation \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_Navigation_small_navigation \<rightarrow> Skip);; (enter_CheckPosition_Navigation_small_navigation \<rightarrow> Transc_Navigation_small_navigation(NID_CheckPosition_Navigation_small_navigation)))))))))
                                          	  \<box>
                                          	  ((n = NID_CheckPosition_Navigation_small_navigation) \<^bold>& ((((position_Navigation_small_navigation < target_Navigation_small_navigation)) \<^bold>& (((internal__Navigation_small_navigation\<^bold>.NID_CheckPosition_Navigation_small_navigation \<rightarrow> (SSTOP \<triangle> (proposal_out\<^bold>!1 \<rightarrow> Skip)));; (enter_WaitMoveApplied_Navigation_small_navigation \<rightarrow> Transc_Navigation_small_navigation(NID_WaitMoveApplied_Navigation_small_navigation))))))))
                                          	  \<box>
                                          	  ((n = NID_CheckPosition_Navigation_small_navigation) \<^bold>& ((((position_Navigation_small_navigation \<ge> target_Navigation_small_navigation)) \<^bold>& (((internal__Navigation_small_navigation\<^bold>.NID_CheckPosition_Navigation_small_navigation \<rightarrow> (SSTOP \<triangle> (proposal_out\<^bold>!0 \<rightarrow> Skip)));; (enter_WaitStopApplied_Navigation_small_navigation \<rightarrow> Transc_Navigation_small_navigation(NID_WaitStopApplied_Navigation_small_navigation))))))))
                                          	  \<box>
                                          	  ((n = NID_WaitMoveApplied_Navigation_small_navigation) \<^bold>& (((OAApplied__in\<^bold>.NID_WaitMoveApplied_Navigation_small_navigation \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_Navigation_small_navigation \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_Navigation_small_navigation \<rightarrow> Skip);; (enter_WaitForPose_Navigation_small_navigation \<rightarrow> Transc_Navigation_small_navigation(NID_WaitForPose_Navigation_small_navigation)))))))))
                                          	  \<box>
                                          	  ((n = NID_WaitStopApplied_Navigation_small_navigation) \<^bold>& (((OAApplied__in\<^bold>.NID_WaitStopApplied_Navigation_small_navigation \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_Navigation_small_navigation \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_Navigation_small_navigation \<rightarrow> (SSTOP \<triangle> (targetReached_out \<rightarrow> Skip)));; (enter_f0_Navigation_small_navigation \<rightarrow> Transc_Navigation_small_navigation(NID_f0_Navigation_small_navigation)))))))))
                                          	  \<box>
                                             	  ((n = NID_f0_Navigation_small_navigation) \<^bold>& ((terminate \<rightarrow> Skip))))))))) "

(* Changed \<cdot> to \<^bold>. because \<cdot> could not be found in the imported library. *)
(* Changed the renamings [ a \<mapsto> b, ... ] to cRename \<lbrace> a \<mapsto> b, ... \<rbrace> because Isabelle cannot parse them in an equation. *)
(* Changed Trans to Trans(NID_i0) because Trans is defined with the current node as a parameter and the generated call gives none; i0 is the initial junction. *)
definition ncCoreBehaviour_Navigation_small_navigation :: "(mychan, unit) cyphyaction" where
" ncCoreBehaviour_Navigation_small_navigation = 	((cRename \<lbrace> share \<mapsto> share \<rbrace> ((cRename
                                                   	 (\<lbrace> interrupt_i0_Navigation_small_navigation \<mapsto> internal__Navigation_small_navigation\<^bold>.NID_i0_Navigation_small_navigation,
                                                   	    interrupt_CheckPosition_Navigation_small_navigation \<mapsto> internal__Navigation_small_navigation\<^bold>.NID_CheckPosition_Navigation_small_navigation,
                                                   	    interrupt_WaitMoveApplied_Navigation_small_navigation \<mapsto> OAApplied__in\<^bold>.NID_WaitMoveApplied_Navigation_small_navigation,
                                                   	    interrupt_WaitStopApplied_Navigation_small_navigation \<mapsto> OAApplied__in\<^bold>.NID_WaitStopApplied_Navigation_small_navigation,
                                                   	    interrupt_f0_Navigation_small_navigation \<mapsto> interrupt_Navigation_small_navigation, interrupt_WaitMoveApplied_Navigation_small_navigation \<mapsto> interrupt_Navigation_small_navigation,
                                                   	    interrupt_WaitTarget_Navigation_small_navigation \<mapsto> interrupt_Navigation_small_navigation, interrupt_WaitForPose_Navigation_small_navigation \<mapsto> interrupt_Navigation_small_navigation,
                                                   	    interrupt_WaitStopApplied_Navigation_small_navigation \<mapsto> interrupt_Navigation_small_navigation \<rbrace> \<union>
                                                   	  \<lbrace> interrupt_WaitTarget_Navigation_small_navigation \<mapsto> setTarget__in (NID_WaitTarget_Navigation_small_navigation, v) | v. True \<rbrace> \<union>
                                                   	  \<lbrace> interrupt_WaitForPose_Navigation_small_navigation \<mapsto> globalpose__in (NID_WaitForPose_Navigation_small_navigation, v) | v. True \<rbrace>)
                                                   	 (composeNodes_Navigation_small_navigation))))
                                                   	  \<lbrakk> \<^bold>0 | \<lbrace> exit_Navigation_small_navigation,enter_WaitForPose_Navigation_small_navigation,internal__Navigation_small_navigation\<^bold>.NID_i0_Navigation_small_navigation,internal__Navigation_small_navigation\<^bold>.NID_CheckPosition_Navigation_small_navigation,setTarget__in\<^bold>.NID_WaitTarget_Navigation_small_navigation,enter_f0_Navigation_small_navigation,globalpose__in\<^bold>.NID_WaitForPose_Navigation_small_navigation,OAApplied__in\<^bold>.NID_WaitMoveApplied_Navigation_small_navigation,interrupt_Navigation_small_navigation,enter_i0_Navigation_small_navigation,enter_WaitStopApplied_Navigation_small_navigation,OAApplied__in\<^bold>.NID_WaitStopApplied_Navigation_small_navigation,share,terminate,enter_WaitMoveApplied_Navigation_small_navigation,exited_Navigation_small_navigation,enter_WaitTarget_Navigation_small_navigation,enter_CheckPosition_Navigation_small_navigation \<rbrace> | \<^bold>0 \<rbrakk>
                                                   	  (cRename \<lbrace> share \<mapsto> share \<rbrace> ((enter_i0_Navigation_small_navigation \<rightarrow> Trans_Navigation_small_navigation(NID_i0_Navigation_small_navigation))))) "

(* Added the state clocks for the timed semantics (reference manual, Rule 88): a clock is reset by the entered
   event of its state, offers its value on get_CLID_<state>, ends on terminate, and otherwise counts the time
   units since the state was entered. StateClocks runs the clocks in parallel, synchronised on terminate
   (Rule 85). *)

recursive
  Clock_CLID_WaitTarget_Navigation_small_navigation :: "nat \<Rightarrow> (mychan, unit) cyphyaction"
where
" Clock_CLID_WaitTarget_Navigation_small_navigation(age) = 	cInitialTimeout1 ((entered_WaitTarget_Navigation_small_navigation \<rightarrow> Clock_CLID_WaitTarget_Navigation_small_navigation(0))
      \<box> (get_CLID_WaitTarget_Navigation_small_navigation\<^bold>!age \<rightarrow> Clock_CLID_WaitTarget_Navigation_small_navigation(age))
      \<box> (terminate \<rightarrow> Skip))
      (Clock_CLID_WaitTarget_Navigation_small_navigation(Suc age)) "

recursive
  Clock_CLID_WaitForPose_Navigation_small_navigation :: "nat \<Rightarrow> (mychan, unit) cyphyaction"
where
" Clock_CLID_WaitForPose_Navigation_small_navigation(age) = 	cInitialTimeout1 ((entered_WaitForPose_Navigation_small_navigation \<rightarrow> Clock_CLID_WaitForPose_Navigation_small_navigation(0))
      \<box> (get_CLID_WaitForPose_Navigation_small_navigation\<^bold>!age \<rightarrow> Clock_CLID_WaitForPose_Navigation_small_navigation(age))
      \<box> (terminate \<rightarrow> Skip))
      (Clock_CLID_WaitForPose_Navigation_small_navigation(Suc age)) "

recursive
  Clock_CLID_WaitMoveApplied_Navigation_small_navigation :: "nat \<Rightarrow> (mychan, unit) cyphyaction"
where
" Clock_CLID_WaitMoveApplied_Navigation_small_navigation(age) = 	cInitialTimeout1 ((entered_WaitMoveApplied_Navigation_small_navigation \<rightarrow> Clock_CLID_WaitMoveApplied_Navigation_small_navigation(0))
      \<box> (get_CLID_WaitMoveApplied_Navigation_small_navigation\<^bold>!age \<rightarrow> Clock_CLID_WaitMoveApplied_Navigation_small_navigation(age))
      \<box> (terminate \<rightarrow> Skip))
      (Clock_CLID_WaitMoveApplied_Navigation_small_navigation(Suc age)) "

recursive
  Clock_CLID_WaitStopApplied_Navigation_small_navigation :: "nat \<Rightarrow> (mychan, unit) cyphyaction"
where
" Clock_CLID_WaitStopApplied_Navigation_small_navigation(age) = 	cInitialTimeout1 ((entered_WaitStopApplied_Navigation_small_navigation \<rightarrow> Clock_CLID_WaitStopApplied_Navigation_small_navigation(0))
      \<box> (get_CLID_WaitStopApplied_Navigation_small_navigation\<^bold>!age \<rightarrow> Clock_CLID_WaitStopApplied_Navigation_small_navigation(age))
      \<box> (terminate \<rightarrow> Skip))
      (Clock_CLID_WaitStopApplied_Navigation_small_navigation(Suc age)) "

definition StateClocks_Navigation_small_navigation :: "(mychan, unit) cyphyaction" where
" StateClocks_Navigation_small_navigation = 	(Clock_CLID_WaitTarget_Navigation_small_navigation(0::nat)
      \<lbrakk> \<^bold>0 | \<lbrace> terminate \<rbrace> | \<^bold>0 \<rbrakk>
      (Clock_CLID_WaitForPose_Navigation_small_navigation(0::nat)
      \<lbrakk> \<^bold>0 | \<lbrace> terminate \<rbrace> | \<^bold>0 \<rbrakk>
      (Clock_CLID_WaitMoveApplied_Navigation_small_navigation(0::nat)
      \<lbrakk> \<^bold>0 | \<lbrace> terminate \<rbrace> | \<^bold>0 \<rbrakk>
      Clock_CLID_WaitStopApplied_Navigation_small_navigation(0::nat)))) "

(* Changed the generated renaming to cRename renameTriggerEvents. *)
definition ncBehaviour_Navigation_small_navigation :: "(mychan, unit) cyphyaction" where
" ncBehaviour_Navigation_small_navigation = 	(cRename renameTriggerEvents_Navigation_small_navigation ((ncCoreBehaviour_Navigation_small_navigation \<Zhide> \<lbrace> enter_i0_Navigation_small_navigation,enter_WaitTarget_Navigation_small_navigation,enter_WaitForPose_Navigation_small_navigation,enter_CheckPosition_Navigation_small_navigation,enter_WaitMoveApplied_Navigation_small_navigation,enter_WaitStopApplied_Navigation_small_navigation,enter_f0_Navigation_small_navigation,exit_Navigation_small_navigation,exited_Navigation_small_navigation,internal__Navigation_small_navigation \<rbrace>))) "

(* Changed \<Zhide> \<lbrace> enteredSS_Navigation_small_navigation \<rbrace> to \<Zhide> enteredSS_in_stmbd_Navigation_small_navigation because only the second name is declared, and it is already a channel set. *)
(* Changed ncBehaviour in machineBody to its composition with the state clocks for the timed semantics
   (reference manual, Rule 76): the semantics of a node container is
   (ncBehaviour |[stateClockSync \<union> {end}|] clocks(stateClocks)) \ (stateClockSync \ {|entered|}), which hides the
   clock reads; machineBody then hides the entered events as in the untimed model (Rule 75). *)
definition machineBody_Navigation_small_navigation :: "(mychan, unit) cyphyaction" where
" machineBody_Navigation_small_navigation = 	((((ncBehaviour_Navigation_small_navigation
                                            	  \<lbrakk> \<^bold>0 | (stateClockSync_Navigation_small_navigation \<union> \<lbrace> terminate \<rbrace>) | \<^bold>0 \<rbrakk>
                                            	  StateClocks_Navigation_small_navigation) \<Zhide> (stateClockSync_Navigation_small_navigation - enteredSS_in_stmbd_Navigation_small_navigation))
                                            	  \<lbrakk> \<^bold>0 | \<lbrace> interrupt_Navigation_small_navigation \<rbrace> | \<^bold>0 \<rbrakk> 
                                               	  Skip) \<Zhide> enteredSS_in_stmbd_Navigation_small_navigation) "

recursive
  Memory_target_Navigation_small_navigation :: "nat \<Rightarrow> (mychan, unit) cyphyaction"
where
" Memory_target_Navigation_small_navigation(value) = 	(((get_target_Navigation_small_navigation\<^bold>!value \<rightarrow> Memory_target_Navigation_small_navigation(value))
                                                     	  \<box>
                                                     	  ((set_target_Navigation_small_navigation\<^bold>?x__v \<rightarrow> Memory_target_Navigation_small_navigation(x__v))
                                                     	  \<box>
                                                        	  (terminate \<rightarrow> Skip)))) "

recursive
  Memory_position_Navigation_small_navigation :: "nat \<Rightarrow> (mychan, unit) cyphyaction"
where
" Memory_position_Navigation_small_navigation(value) = 	(((get_position_Navigation_small_navigation\<^bold>!value \<rightarrow> Memory_position_Navigation_small_navigation(value))
                                                       	  \<box>
                                                       	  ((set_position_Navigation_small_navigation\<^bold>?x__v \<rightarrow> Memory_position_Navigation_small_navigation(x__v))
                                                       	  \<box>
                                                          	  (terminate \<rightarrow> Skip)))) "

(* Changed (0) to (0::nat) because each equation is type-checked on its own; without the type, Memory_target and Memory_position here are not matched to their definitions. *)
definition varMemory_Navigation_small_navigation :: "(mychan, unit) cyphyaction" where
" varMemory_Navigation_small_navigation = 	(Memory_target_Navigation_small_navigation((0::nat))
                                          	  \<lbrakk> \<^bold>0 | \<lbrace> terminate \<rbrace> | \<^bold>0 \<rbrakk> 
                                             	  Memory_position_Navigation_small_navigation((0::nat))) "

definition stateful_Navigation_small_navigation :: "(mychan, unit) cyphyaction" where
" stateful_Navigation_small_navigation = 	((machineBody_Navigation_small_navigation
                                            	  \<lbrakk> \<^bold>0 | \<lbrace> get_position_Navigation_small_navigation,get_target_Navigation_small_navigation,terminate,set_position_Navigation_small_navigation,set_target_Navigation_small_navigation \<rbrace> | \<^bold>0 \<rbrakk>
                                            	  varMemory_Navigation_small_navigation) \<Zhide> \<lbrace> get_position_Navigation_small_navigation,get_target_Navigation_small_navigation,set_position_Navigation_small_navigation,set_target_Navigation_small_navigation \<rbrace>) "

definition sharedVarMemory_Navigation_small_navigation :: "(mychan, unit) cyphyaction" where
" sharedVarMemory_Navigation_small_navigation = 	(terminate \<rightarrow> Skip) "

(* Changed [ ] to cRename ({} :: mychan \<leftrightarrow> mychan) (the relation type of cRename is not fixed by the process), \<lbrace> shared \<rbrace> to the declared channel set, and \<lbrace> \<rbrace> to ({} :: mychan set). *)
definition stm_Navigation_small_navigation :: "(mychan, unit) cyphyaction" where
" stm_Navigation_small_navigation = 	((((cRename ({} :: mychan \<leftrightarrow> mychan) (((stateful_Navigation_small_navigation \<Zhide> \<lbrace> terminate \<rbrace>);; (SSTOP \<triangle> (terminate \<rightarrow> Skip)))))
                                       	  \<lbrakk> \<^bold>0 | shared_variable_events_in_stmbd_Navigation_small_navigation | \<^bold>0 \<rbrakk>
                                       	  Skip)
                                       	  \<lbrakk> \<^bold>0 | \<lbrace> terminate \<rbrace> | \<^bold>0 \<rbrakk>
                                       	  sharedVarMemory_Navigation_small_navigation) \<Zhide> ({} :: mychan set)) "

(* Added Small_Navigation_Timed as the name of the whole model, with maximal progress for the timed semantics. The
   reference manual has no rule for it; the RoboChart paper has prioritise(P, <{}, {tock}>) on the machine
   process (Section 6.3.1, p. 3142), and RoboTool has
   D__ = timed_priority(STM \ union(internal_events, localClockResets)) (robochart-csp-gen,
   CTimedStateMachineGenerator, compileStateMachineBehaviours), where FDR's timed_priority(P) is
   prioritise(P, <{}, {tock}>) (controllers and modules carry prioritise(P, <visibleMemoryEvents, {tock}>)
   themselves), so internal events happen before time passes. stm already hides or blocks every event of
   internal_events and the machine declares no clock, so cPrioritise {} is applied to stm as it is. *)
definition Small_Navigation_Timed :: "(mychan, unit) cyphyaction" where
  "Small_Navigation_Timed = cPrioritise {} stm_Navigation_small_navigation"

setup \<open>Sign.parent_path\<close>

end
