
theory IsaCircus_enriched_Rescue_03112026_134717 
	imports "Test_Generation.Ax_CyPhyCircus" Action_Command_Compat
begin

subsection \<open> Prelude \<close>

declare [[literal_variables]]
unbundle Circus_Syntax

hide_const (open) sum

subsection \<open> Model \<close>


	
	
datatype NIDS_stm_ref0_Finder_Rescue = 
	NID_i0_stm_ref0_Finder_Rescue | 
	NID_Off_stm_ref0_Finder_Rescue | 
	NID_Looking_stm_ref0_Finder_Rescue | 
	NID_Delivering_stm_ref0_Finder_Rescue | 
	NID_Returning_stm_ref0_Finder_Rescue


\<comment> \<open>constant and function declaration/definition\<close>
consts LV_stm_ref0_Finder_Rescue :: "nat"
	
definition TOP_stm_ref0_Finder_Rescue :: "nat"
where "TOP_stm_ref0_Finder_Rescue = 1"
	
definition DELIVERY_stm_ref0_Finder_Rescue :: "nat"
where "DELIVERY_stm_ref0_Finder_Rescue = 2"
	

\<comment> \<open>Channel Declaration\<close>
chantype mychan = 
share :: unit
\<comment> \<open>terminate_channel\<close>

terminate :: unit 
	
\<comment> \<open>event_channel_pltf_Rescue\<close>
	
\<comment> \<open>undefined_op_channel_pltf_Rescue\<close>

moveCall :: "nat"

turnBackCall :: unit 
	
\<comment> \<open>var_channels_pltf_Rescue\<close>
	
\<comment> \<open>var_channels_ctrl_Finder_Rescue\<close>
	
\<comment> \<open>event_channel_ctrl_Finder_Rescue\<close>

origin_in :: unit 
origin_out :: unit 

found_in :: unit 
found_out :: unit 

land_in :: unit 
land_out :: unit 

takeoff_in :: unit 
takeoff_out :: unit 
	
\<comment> \<open>undefined_op_channel_ctrl_Finder_Rescue\<close>

moveCall :: "nat"

turnBackCall :: unit 
	
\<comment> \<open>internal_channel_stmbd_stm_ref0_Finder_Rescue\<close>

internal__stm_ref0_Finder_Rescue :: "NIDS_stm_ref0_Finder_Rescue"
	
\<comment> \<open>flowchannel_stmbd_stm_ref0_Finder_Rescue\<close>

interrupt_stm_ref0_Finder_Rescue :: unit 
exited_stm_ref0_Finder_Rescue :: unit 
exit_stm_ref0_Finder_Rescue :: unit 
	
\<comment> \<open>var_channel_stmbd_stm_ref0_Finder_Rescue\<close>
	
\<comment> \<open>event_channel_stmbd_stm_ref0_Finder_Rescue\<close>

origin_in :: unit 
origin_out :: unit 

found_in :: unit 
found_out :: unit 

land_in :: unit 
land_out :: unit 

takeoff_in :: unit 
takeoff_out :: unit 

origin__in :: "NIDS_stm_ref0_Finder_Rescue"

found__in :: "NIDS_stm_ref0_Finder_Rescue"

land__in :: "NIDS_stm_ref0_Finder_Rescue"

takeoff__in :: "NIDS_stm_ref0_Finder_Rescue"
	
\<comment> \<open>undefined_op_channel_stmbd_stm_ref0_Finder_Rescue\<close>

moveCall :: "nat"

turnBackCall :: unit 
	
\<comment> \<open>junction_channel_in_stmbd_i0_stm_ref0_Finder_Rescue\<close>

enter_i0_stm_ref0_Finder_Rescue :: unit 
interrupt_i0_stm_ref0_Finder_Rescue :: unit 
	
\<comment> \<open>state_channel_in_stmbd_Off_stm_ref0_Finder_Rescue\<close>

enter_Off_stm_ref0_Finder_Rescue :: unit 
entered_Off_stm_ref0_Finder_Rescue :: unit 
interrupt_Off_stm_ref0_Finder_Rescue :: unit 
enteredL_Off_stm_ref0_Finder_Rescue :: unit 
enteredR_Off_stm_ref0_Finder_Rescue :: unit 
	
\<comment> \<open>state_channel_in_stmbd_Looking_stm_ref0_Finder_Rescue\<close>

enter_Looking_stm_ref0_Finder_Rescue :: unit 
entered_Looking_stm_ref0_Finder_Rescue :: unit 
interrupt_Looking_stm_ref0_Finder_Rescue :: unit 
enteredL_Looking_stm_ref0_Finder_Rescue :: unit 
enteredR_Looking_stm_ref0_Finder_Rescue :: unit 
	
\<comment> \<open>state_channel_in_stmbd_Delivering_stm_ref0_Finder_Rescue\<close>

enter_Delivering_stm_ref0_Finder_Rescue :: unit 
entered_Delivering_stm_ref0_Finder_Rescue :: unit 
interrupt_Delivering_stm_ref0_Finder_Rescue :: unit 
enteredL_Delivering_stm_ref0_Finder_Rescue :: unit 
enteredR_Delivering_stm_ref0_Finder_Rescue :: unit 
	
\<comment> \<open>state_channel_in_stmbd_Returning_stm_ref0_Finder_Rescue\<close>

enter_Returning_stm_ref0_Finder_Rescue :: unit 
entered_Returning_stm_ref0_Finder_Rescue :: unit 
interrupt_Returning_stm_ref0_Finder_Rescue :: unit 
enteredL_Returning_stm_ref0_Finder_Rescue :: unit 
enteredR_Returning_stm_ref0_Finder_Rescue :: unit 
	
\<comment> \<open>assumption-guarantee_viol_stm_ref0_Finder_Rescue\<close>

aviol :: unit 
gviol :: unit 
	


\<comment> \<open>ChannelSet Decleration\<close>
	
definition "shared_variable_events_ctrl_Finder_Rescue = ({} :: mychan set)"	
definition "enterSS_in_stmbd_stm_ref0_Finder_Rescue = \<lbrace> 
	  enter_i0_stm_ref0_Finder_Rescue, 
	  enter_Off_stm_ref0_Finder_Rescue, 
	  enter_Looking_stm_ref0_Finder_Rescue, 
	  enter_Delivering_stm_ref0_Finder_Rescue, 
	  enter_Returning_stm_ref0_Finder_Rescue \<rbrace>"	
definition "enteredSS_in_stmbd_stm_ref0_Finder_Rescue = \<lbrace> 
	  entered_Returning_stm_ref0_Finder_Rescue, 
	  entered_Looking_stm_ref0_Finder_Rescue, 
	  entered_Delivering_stm_ref0_Finder_Rescue, 
	  entered_Off_stm_ref0_Finder_Rescue \<rbrace>"	
definition "internal_events_in_stmbd_stm_ref0_Finder_Rescue = \<lbrace> 
	  enter_i0_stm_ref0_Finder_Rescue, 
	  enter_Off_stm_ref0_Finder_Rescue, 
	  enter_Looking_stm_ref0_Finder_Rescue, 
	  enter_Delivering_stm_ref0_Finder_Rescue, 
	  enter_Returning_stm_ref0_Finder_Rescue, 
	  entered_Returning_stm_ref0_Finder_Rescue, 
	  entered_Looking_stm_ref0_Finder_Rescue, 
	  entered_Delivering_stm_ref0_Finder_Rescue, 
	  entered_Off_stm_ref0_Finder_Rescue, 
	  interrupt_stm_ref0_Finder_Rescue, 
	  exited_stm_ref0_Finder_Rescue \<rbrace>"	
definition "shared_variable_events_in_stmbd_stm_ref0_Finder_Rescue = ({} :: mychan set)"	
definition "sem__events_stm_stm_ref0_Finder_Rescue = \<lbrace> 
	  terminate, 
	  moveCall, 
	  turnBackCall \<rbrace>"
definition relu :: "real \<Rightarrow> real" where
		   "relu x = max 0 x"

definition norm :: "real \<Rightarrow> (real \<times> real) \<Rightarrow> (real \<times> real) \<Rightarrow> real" where
		   "norm x r r' = (((x - fst(r)) / (snd(r) - fst(r))) 
                              * (snd(r') - fst(r'))) + fst(r')"
                              
abbreviation "assume b Q P \<equiv> (if b then P else aviol \<rightarrow> Q)"
abbreviation "guar b P \<equiv> (if b then P else gviol \<rightarrow> Stop)"

definition project_triggers_stm_ref0_Finder_Rescue :: "(mychan \<times> mychan) set" where
  "project_triggers_stm_ref0_Finder_Rescue = \<lbrace> origin__in n \<mapsto> origin_in () | n. True \<rbrace> \<union>
     \<lbrace> found__in n \<mapsto> found_in () | n. True \<rbrace>"
actions  is "(mychan, unit) cyphyaction" where 
"SSTOP = share  \<rightarrow>  SSTOP" |
" CALL__move(lv) = 	((moveCall\<^bold>.lv \<rightarrow> Skip)) "
 | " CALL__turnBack = 	(turnBackCall \<rightarrow> Skip) "
 | " InactiveJct_i0_stm_ref0_Finder_Rescue = 	(SSTOP \<triangle> (Activation_i0_stm_ref0_Finder_Rescue
                                             	  \<box>
                                             	  Termination_i0_stm_ref0_Finder_Rescue)) "
 | " Activation_i0_stm_ref0_Finder_Rescue = 	(enter_i0_stm_ref0_Finder_Rescue \<rightarrow> Active_i0_stm_ref0_Finder_Rescue) "
 | " Termination_i0_stm_ref0_Finder_Rescue = 	(terminate \<rightarrow> Skip) "
 | " Active_i0_stm_ref0_Finder_Rescue = 	((SSTOP \<triangle> (interrupt_i0_stm_ref0_Finder_Rescue \<rightarrow> Skip));; InactiveJct_i0_stm_ref0_Finder_Rescue) "
 | " Inactive_Off_stm_ref0_Finder_Rescue = 	(SSTOP \<triangle> (Activation_Off_stm_ref0_Finder_Rescue
                                           	  \<box>
                                           	  Termination_Off_stm_ref0_Finder_Rescue)) "
 | " Activation_Off_stm_ref0_Finder_Rescue = 	(enter_Off_stm_ref0_Finder_Rescue \<rightarrow> Active_Off_stm_ref0_Finder_Rescue) "
 | " Termination_Off_stm_ref0_Finder_Rescue = 	(terminate \<rightarrow> Skip) "
 | " Active_Off_stm_ref0_Finder_Rescue = 	(Skip;; (Behaviour_Off_stm_ref0_Finder_Rescue;; Exiting_Off_stm_ref0_Finder_Rescue)) "
 | " Behaviour_Off_stm_ref0_Finder_Rescue = 	(entered_Off_stm_ref0_Finder_Rescue \<rightarrow> During_Off_stm_ref0_Finder_Rescue) "
 | " During_Off_stm_ref0_Finder_Rescue = 	((Skip;; SSTOP) \<triangle> (interrupt_Off_stm_ref0_Finder_Rescue \<rightarrow> Skip)) "
 | " Exiting_Off_stm_ref0_Finder_Rescue = 	((SSTOP \<triangle> (exit_stm_ref0_Finder_Rescue \<rightarrow> Skip));; (Skip;; (exited_stm_ref0_Finder_Rescue \<rightarrow> Inactive_Off_stm_ref0_Finder_Rescue))) "
 | " Inactive_Looking_stm_ref0_Finder_Rescue = 	(SSTOP \<triangle> (Activation_Looking_stm_ref0_Finder_Rescue
                                               	  \<box>
                                               	  Termination_Looking_stm_ref0_Finder_Rescue)) "
 | " Activation_Looking_stm_ref0_Finder_Rescue = 	(enter_Looking_stm_ref0_Finder_Rescue \<rightarrow> Active_Looking_stm_ref0_Finder_Rescue) "
 | " Termination_Looking_stm_ref0_Finder_Rescue = 	(terminate \<rightarrow> Skip) "
 | " Active_Looking_stm_ref0_Finder_Rescue = 	(CALL__move(LV_stm_ref0_Finder_Rescue);; (Behaviour_Looking_stm_ref0_Finder_Rescue;; Exiting_Looking_stm_ref0_Finder_Rescue)) "
 | " Behaviour_Looking_stm_ref0_Finder_Rescue = 	(entered_Looking_stm_ref0_Finder_Rescue \<rightarrow> During_Looking_stm_ref0_Finder_Rescue) "
 | " During_Looking_stm_ref0_Finder_Rescue = 	((Skip;; SSTOP) \<triangle> (interrupt_Looking_stm_ref0_Finder_Rescue \<rightarrow> Skip)) "
 | " Exiting_Looking_stm_ref0_Finder_Rescue = 	((SSTOP \<triangle> (exit_stm_ref0_Finder_Rescue \<rightarrow> Skip));; (Skip;; (exited_stm_ref0_Finder_Rescue \<rightarrow> Inactive_Looking_stm_ref0_Finder_Rescue))) "
 | " Inactive_Delivering_stm_ref0_Finder_Rescue = 	(SSTOP \<triangle> (Activation_Delivering_stm_ref0_Finder_Rescue
                                                  	  \<box>
                                                  	  Termination_Delivering_stm_ref0_Finder_Rescue)) "
 | " Activation_Delivering_stm_ref0_Finder_Rescue = 	(enter_Delivering_stm_ref0_Finder_Rescue \<rightarrow> Active_Delivering_stm_ref0_Finder_Rescue) "
 | " Termination_Delivering_stm_ref0_Finder_Rescue = 	(terminate \<rightarrow> Skip) "
 | " Active_Delivering_stm_ref0_Finder_Rescue = 	((SSTOP \<triangle> Skip);; (Behaviour_Delivering_stm_ref0_Finder_Rescue;; Exiting_Delivering_stm_ref0_Finder_Rescue)) "
 | " Behaviour_Delivering_stm_ref0_Finder_Rescue = 	(entered_Delivering_stm_ref0_Finder_Rescue \<rightarrow> During_Delivering_stm_ref0_Finder_Rescue) "
 | " During_Delivering_stm_ref0_Finder_Rescue = 	((Skip;; SSTOP) \<triangle> (interrupt_Delivering_stm_ref0_Finder_Rescue \<rightarrow> Skip)) "
 | " Exiting_Delivering_stm_ref0_Finder_Rescue = 	((SSTOP \<triangle> (exit_stm_ref0_Finder_Rescue \<rightarrow> Skip));; (Skip;; (exited_stm_ref0_Finder_Rescue \<rightarrow> Inactive_Delivering_stm_ref0_Finder_Rescue))) "
 | " Inactive_Returning_stm_ref0_Finder_Rescue = 	(SSTOP \<triangle> (Activation_Returning_stm_ref0_Finder_Rescue
                                                 	  \<box>
                                                 	  Termination_Returning_stm_ref0_Finder_Rescue)) "
 | " Activation_Returning_stm_ref0_Finder_Rescue = 	(enter_Returning_stm_ref0_Finder_Rescue \<rightarrow> Active_Returning_stm_ref0_Finder_Rescue) "
 | " Termination_Returning_stm_ref0_Finder_Rescue = 	(terminate \<rightarrow> Skip) "
 | " Active_Returning_stm_ref0_Finder_Rescue = 	(Skip;; (Behaviour_Returning_stm_ref0_Finder_Rescue;; Exiting_Returning_stm_ref0_Finder_Rescue)) "
 | " Behaviour_Returning_stm_ref0_Finder_Rescue = 	(entered_Returning_stm_ref0_Finder_Rescue \<rightarrow> During_Returning_stm_ref0_Finder_Rescue) "
 | " During_Returning_stm_ref0_Finder_Rescue = 	((Skip;; SSTOP) \<triangle> (interrupt_Returning_stm_ref0_Finder_Rescue \<rightarrow> Skip)) "
 | " Exiting_Returning_stm_ref0_Finder_Rescue = 	((SSTOP \<triangle> (exit_stm_ref0_Finder_Rescue \<rightarrow> Skip));; (Skip;; (exited_stm_ref0_Finder_Rescue \<rightarrow> Inactive_Returning_stm_ref0_Finder_Rescue))) "
 | " composeNodes_stm_ref0_Finder_Rescue = 	((((Inactive_Looking_stm_ref0_Finder_Rescue
                                           	  \<lbrakk> \<^bold>0 | \<lbrace> share,terminate \<rbrace> | \<^bold>0 \<rbrakk> 
                                           	  Inactive_Delivering_stm_ref0_Finder_Rescue)
                                           	  \<lbrakk> \<^bold>0 | \<lbrace> share,terminate \<rbrace> | \<^bold>0 \<rbrakk> 
                                           	  InactiveJct_i0_stm_ref0_Finder_Rescue)
                                           	  \<lbrakk> \<^bold>0 | \<lbrace> share,terminate \<rbrace> | \<^bold>0 \<rbrakk> 
                                           	  Inactive_Returning_stm_ref0_Finder_Rescue)
                                           	  \<lbrakk> \<^bold>0 | \<lbrace> share,terminate \<rbrace> | \<^bold>0 \<rbrakk> 
                                           	  Inactive_Off_stm_ref0_Finder_Rescue) "
 | " Trans_stm_ref0_Finder_Rescue(n) = 	((assume True (Trans_stm_ref0_Finder_Rescue(n)) ((((((((n = NID_Off_stm_ref0_Finder_Rescue) \<^bold>& (((internal__stm_ref0_Finder_Rescue\<^bold>.NID_Off_stm_ref0_Finder_Rescue \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_stm_ref0_Finder_Rescue \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_stm_ref0_Finder_Rescue \<rightarrow> ((SSTOP \<triangle> (takeoff_out \<rightarrow> Skip));; (SSTOP \<triangle> Skip)));; (enter_Looking_stm_ref0_Finder_Rescue \<rightarrow> Trans_stm_ref0_Finder_Rescue(NID_Looking_stm_ref0_Finder_Rescue))))))))
                                       	  \<box>
                                       	  ((n = NID_Looking_stm_ref0_Finder_Rescue) \<^bold>& (((found__in\<^bold>.NID_Looking_stm_ref0_Finder_Rescue \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_stm_ref0_Finder_Rescue \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_stm_ref0_Finder_Rescue \<rightarrow> (SSTOP \<triangle> (land_out \<rightarrow> Skip)));; (enter_Delivering_stm_ref0_Finder_Rescue \<rightarrow> Trans_stm_ref0_Finder_Rescue(NID_Delivering_stm_ref0_Finder_Rescue)))))))))
                                       	  \<box>
                                       	  ((n = NID_Delivering_stm_ref0_Finder_Rescue) \<^bold>& (((internal__stm_ref0_Finder_Rescue\<^bold>.NID_Delivering_stm_ref0_Finder_Rescue \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_stm_ref0_Finder_Rescue \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_stm_ref0_Finder_Rescue \<rightarrow> ((SSTOP \<triangle> (takeoff_out \<rightarrow> Skip));; ((SSTOP \<triangle> Skip);; (CALL__turnBack;; CALL__move(LV_stm_ref0_Finder_Rescue)))));; (enter_Returning_stm_ref0_Finder_Rescue \<rightarrow> Trans_stm_ref0_Finder_Rescue(NID_Returning_stm_ref0_Finder_Rescue)))))))))
                                       	  \<box>
                                       	  ((n = NID_i0_stm_ref0_Finder_Rescue) \<^bold>& (((internal__stm_ref0_Finder_Rescue\<^bold>.NID_i0_stm_ref0_Finder_Rescue \<rightarrow> Skip);; (enter_Off_stm_ref0_Finder_Rescue \<rightarrow> Trans_stm_ref0_Finder_Rescue(NID_Off_stm_ref0_Finder_Rescue))))))
                                       	  \<box>
                                       	  ((n = NID_Returning_stm_ref0_Finder_Rescue) \<^bold>& (((origin__in\<^bold>.NID_Returning_stm_ref0_Finder_Rescue \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_stm_ref0_Finder_Rescue \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_stm_ref0_Finder_Rescue \<rightarrow> (CALL__turnBack;; (SSTOP \<triangle> (land_out \<rightarrow> Skip))));; (enter_Off_stm_ref0_Finder_Rescue \<rightarrow> Trans_stm_ref0_Finder_Rescue(NID_Off_stm_ref0_Finder_Rescue)))))))))
                                       	  \<box>
                                       	  (share \<rightarrow> Trans_stm_ref0_Finder_Rescue(n)))
                                       	  \<box>
                                       	  (((interrupt_stm_ref0_Finder_Rescue \<rightarrow> (SSTOP \<triangle> (exit_stm_ref0_Finder_Rescue \<rightarrow> Skip)));; (SSTOP \<triangle> (exited_stm_ref0_Finder_Rescue \<rightarrow> (terminate \<rightarrow> Skip))))
                                       	  \<box>
                                       	  (terminate \<rightarrow> Skip))))) "
 | " Transc_stm_ref0_Finder_Rescue(n) = 	((assume True (Transc_stm_ref0_Finder_Rescue(n)) ((((((n = NID_Off_stm_ref0_Finder_Rescue) \<^bold>& (((internal__stm_ref0_Finder_Rescue\<^bold>.NID_Off_stm_ref0_Finder_Rescue \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_stm_ref0_Finder_Rescue \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_stm_ref0_Finder_Rescue \<rightarrow> ((SSTOP \<triangle> (takeoff_out \<rightarrow> Skip));; (SSTOP \<triangle> Skip)));; (enter_Looking_stm_ref0_Finder_Rescue \<rightarrow> Transc_stm_ref0_Finder_Rescue(NID_Looking_stm_ref0_Finder_Rescue))))))))
                                        	  \<box>
                                        	  ((n = NID_Looking_stm_ref0_Finder_Rescue) \<^bold>& (((found__in\<^bold>.NID_Looking_stm_ref0_Finder_Rescue \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_stm_ref0_Finder_Rescue \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_stm_ref0_Finder_Rescue \<rightarrow> (SSTOP \<triangle> (land_out \<rightarrow> Skip)));; (enter_Delivering_stm_ref0_Finder_Rescue \<rightarrow> Transc_stm_ref0_Finder_Rescue(NID_Delivering_stm_ref0_Finder_Rescue)))))))))
                                        	  \<box>
                                        	  ((n = NID_Delivering_stm_ref0_Finder_Rescue) \<^bold>& (((internal__stm_ref0_Finder_Rescue\<^bold>.NID_Delivering_stm_ref0_Finder_Rescue \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_stm_ref0_Finder_Rescue \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_stm_ref0_Finder_Rescue \<rightarrow> ((SSTOP \<triangle> (takeoff_out \<rightarrow> Skip));; ((SSTOP \<triangle> Skip);; (CALL__turnBack;; CALL__move(LV_stm_ref0_Finder_Rescue)))));; (enter_Returning_stm_ref0_Finder_Rescue \<rightarrow> Transc_stm_ref0_Finder_Rescue(NID_Returning_stm_ref0_Finder_Rescue)))))))))
                                        	  \<box>
                                        	  ((n = NID_i0_stm_ref0_Finder_Rescue) \<^bold>& (((internal__stm_ref0_Finder_Rescue\<^bold>.NID_i0_stm_ref0_Finder_Rescue \<rightarrow> Skip);; (enter_Off_stm_ref0_Finder_Rescue \<rightarrow> Transc_stm_ref0_Finder_Rescue(NID_Off_stm_ref0_Finder_Rescue))))))
                                        	  \<box>
                                        	  ((n = NID_Returning_stm_ref0_Finder_Rescue) \<^bold>& (((origin__in\<^bold>.NID_Returning_stm_ref0_Finder_Rescue \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_stm_ref0_Finder_Rescue \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_stm_ref0_Finder_Rescue \<rightarrow> (CALL__turnBack;; (SSTOP \<triangle> (land_out \<rightarrow> Skip))));; (enter_Off_stm_ref0_Finder_Rescue \<rightarrow> Transc_stm_ref0_Finder_Rescue(NID_Off_stm_ref0_Finder_Rescue))))))))))) "
 | " ncCoreBehaviour_stm_ref0_Finder_Rescue = 	((cRename \<lbrace> share \<mapsto> share \<rbrace> ((cRename \<lbrace> interrupt_Off_stm_ref0_Finder_Rescue \<mapsto> internal__stm_ref0_Finder_Rescue\<^bold>.NID_Off_stm_ref0_Finder_Rescue,
                                              	     interrupt_Looking_stm_ref0_Finder_Rescue \<mapsto> found__in\<^bold>.NID_Looking_stm_ref0_Finder_Rescue,
                                              	     interrupt_Delivering_stm_ref0_Finder_Rescue \<mapsto> internal__stm_ref0_Finder_Rescue\<^bold>.NID_Delivering_stm_ref0_Finder_Rescue,
                                              	     interrupt_i0_stm_ref0_Finder_Rescue \<mapsto> internal__stm_ref0_Finder_Rescue\<^bold>.NID_i0_stm_ref0_Finder_Rescue,
                                              	     interrupt_Returning_stm_ref0_Finder_Rescue \<mapsto> origin__in\<^bold>.NID_Returning_stm_ref0_Finder_Rescue,
                                              	     interrupt_Returning_stm_ref0_Finder_Rescue \<mapsto> interrupt_stm_ref0_Finder_Rescue,
                                              	     interrupt_Looking_stm_ref0_Finder_Rescue \<mapsto> interrupt_stm_ref0_Finder_Rescue,
                                              	     interrupt_Delivering_stm_ref0_Finder_Rescue \<mapsto> interrupt_stm_ref0_Finder_Rescue,
                                              	     interrupt_Off_stm_ref0_Finder_Rescue \<mapsto> interrupt_stm_ref0_Finder_Rescue \<rbrace> (composeNodes_stm_ref0_Finder_Rescue))))
                                              	  \<lbrakk> \<^bold>0 | \<lbrace> found__in\<^bold>.NID_Looking_stm_ref0_Finder_Rescue,enter_Delivering_stm_ref0_Finder_Rescue,enter_Returning_stm_ref0_Finder_Rescue,internal__stm_ref0_Finder_Rescue\<^bold>.NID_Off_stm_ref0_Finder_Rescue,enter_Off_stm_ref0_Finder_Rescue,internal__stm_ref0_Finder_Rescue\<^bold>.NID_Delivering_stm_ref0_Finder_Rescue,interrupt_stm_ref0_Finder_Rescue,enter_Looking_stm_ref0_Finder_Rescue,internal__stm_ref0_Finder_Rescue\<^bold>.NID_i0_stm_ref0_Finder_Rescue,origin__in\<^bold>.NID_Returning_stm_ref0_Finder_Rescue,exited_stm_ref0_Finder_Rescue,exit_stm_ref0_Finder_Rescue,share,terminate,enter_i0_stm_ref0_Finder_Rescue \<rbrace> | \<^bold>0 \<rbrakk> 
                                              	  (cRename \<lbrace> share \<mapsto> share \<rbrace> ((enter_i0_stm_ref0_Finder_Rescue \<rightarrow> Trans_stm_ref0_Finder_Rescue(NID_i0_stm_ref0_Finder_Rescue))))) "
 | " ncBehaviour_stm_ref0_Finder_Rescue = 	(cRename project_triggers_stm_ref0_Finder_Rescue ((ncCoreBehaviour_stm_ref0_Finder_Rescue \<Zhide> \<lbrace> enter_i0_stm_ref0_Finder_Rescue,enter_Off_stm_ref0_Finder_Rescue,enter_Looking_stm_ref0_Finder_Rescue,enter_Delivering_stm_ref0_Finder_Rescue,enter_Returning_stm_ref0_Finder_Rescue,exit_stm_ref0_Finder_Rescue,exited_stm_ref0_Finder_Rescue,internal__stm_ref0_Finder_Rescue \<rbrace>))) "
 | " machineBody_stm_ref0_Finder_Rescue = 	((ncBehaviour_stm_ref0_Finder_Rescue
                                          	  \<lbrakk> \<^bold>0 | \<lbrace> interrupt_stm_ref0_Finder_Rescue \<rbrace> | \<^bold>0 \<rbrakk> 
                                          	  Skip) \<Zhide> enteredSS_in_stmbd_stm_ref0_Finder_Rescue) "
 | " varMemory_stm_ref0_Finder_Rescue = 	(terminate \<rightarrow> Skip) "
 | " stateful_stm_ref0_Finder_Rescue = 	((machineBody_stm_ref0_Finder_Rescue
                                       	  \<lbrakk> \<^bold>0 | \<lbrace> terminate \<rbrace> | \<^bold>0 \<rbrakk> 
                                       	  varMemory_stm_ref0_Finder_Rescue) \<Zhide> ({} :: mychan set)) "
 | " sharedVarMemory_stm_ref0_Finder_Rescue = 	(terminate \<rightarrow> Skip) "
 | " stm_stm_ref0_Finder_Rescue = 	((((cRename ({} :: mychan \<leftrightarrow> mychan) (((stateful_stm_ref0_Finder_Rescue \<Zhide> \<lbrace> terminate \<rbrace>);; (SSTOP \<triangle> (terminate \<rightarrow> Skip)))))
                                  	  \<lbrakk> \<^bold>0 | shared_variable_events_in_stmbd_stm_ref0_Finder_Rescue | \<^bold>0 \<rbrakk> 
                                  	  Skip)
                                  	  \<lbrakk> \<^bold>0 | \<lbrace> terminate \<rbrace> | \<^bold>0 \<rbrakk> 
                                  	  sharedVarMemory_stm_ref0_Finder_Rescue) \<Zhide> ({} :: mychan set)) "
 | " composeMachines_Finder_Rescue = 	(cRename ({} :: mychan \<leftrightarrow> mychan) (stm_stm_ref0_Finder_Rescue)) "
 | " crtlMemory_Finder_Rescue = 	((terminate \<rightarrow> Skip)) "
 | " controller_action_Finder_Rescue = 	((composeMachines_Finder_Rescue
                                       	  \<lbrakk> \<^bold>0 | \<lbrace> terminate \<rbrace> | \<^bold>0 \<rbrakk> 
                                       	  crtlMemory_Finder_Rescue) \<Zhide> ({} :: mychan set)) "
 | " modMemory_action_Rescue = 	((terminate \<rightarrow> Skip)) "
 | " controller_proc_Finder_Rescue = controller_action_Finder_Rescue "
 | " composeControllers_Rescue = (cRename \<lbrace> origin \<mapsto> origin,
                                      found \<mapsto> found,
                                      land \<mapsto> land,
                                      takeoff \<mapsto> takeoff \<rbrace> (controller_proc_Finder_Rescue)) "
 | " modMemory_Rescue = modMemory_action_Rescue "
 | " RCModule_Rescue = ((modMemory_Rescue \<lbrakk> \<^bold>0 | ({} :: mychan set) | \<^bold>0 \<rbrakk> composeControllers_Rescue) \<Zhide> \<lbrace> terminate \<rbrace>) "
end



