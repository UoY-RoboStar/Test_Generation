theory Small_Navigation_Mutant
  imports Small_Navigation
begin

text \<open>The mutant repeats only the action block of the nominal model. The channel sets and
  the renaming relation used by that block are those of the nominal model; its remaining
  constants are hidden so that the action block can declare them again.\<close>

setup \<open>fn thy =>
  let
    val shared = map (prefix "Small_Navigation.Navigation.")
      ["enteredSS_in_stmbd_Navigation_small_navigation",
       "shared_variable_events_in_stmbd_Navigation_small_navigation",
       "project_triggers_Navigation_small_navigation"]
  in
    fold (Sign.hide_const false)
      (map #1 (#constants (Consts.dest (Sign.consts_of thy)))
        |> filter (String.isPrefix "Small_Navigation.Navigation.")
        |> filter_out (member (op =) shared)) thy
  end\<close>

(* namespace to avoid conflict with mutant/original robochart model *)
setup \<open>Sign.add_path "Navigation"\<close>

abbreviation "assume b Q P \<equiv> (if b then P else aviol \<rightarrow> Q)"

(* The equations below carry the same changes from the generated text as Small_Navigation.thy; see the comments there. *)
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

" Trans_Navigation_small_navigation(n) = 	((SSTOP \<triangle> (get_position_Navigation_small_navigation\<^bold>?position_Navigation_small_navigation \<rightarrow> (get_target_Navigation_small_navigation\<^bold>?target_Navigation_small_navigation \<rightarrow> (assume True (Trans_Navigation_small_navigation(n)) ((((((((((n = NID_i0_Navigation_small_navigation) \<^bold>& (((internal__Navigation_small_navigation\<^bold>.NID_i0_Navigation_small_navigation \<rightarrow> Skip);; (enter_WaitTarget_Navigation_small_navigation \<rightarrow> Trans_Navigation_small_navigation(NID_WaitTarget_Navigation_small_navigation)))))
                                         	  \<box>
                                         	  ((n = NID_WaitTarget_Navigation_small_navigation) \<^bold>& (((setTarget__in\<^bold>.NID_WaitTarget_Navigation_small_navigation\<^bold>?target_Navigation_small_navigation \<rightarrow> (SSTOP \<triangle> (set_target_Navigation_small_navigation\<^bold>!target_Navigation_small_navigation \<rightarrow> Skip)));; ((SSTOP \<triangle> (exit_Navigation_small_navigation \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_Navigation_small_navigation \<rightarrow> Skip);; (enter_WaitForPose_Navigation_small_navigation \<rightarrow> Trans_Navigation_small_navigation(NID_WaitForPose_Navigation_small_navigation)))))))))
                                         	  \<box>
                                         	  ((n = NID_WaitForPose_Navigation_small_navigation) \<^bold>& (((globalpose__in\<^bold>.NID_WaitForPose_Navigation_small_navigation\<^bold>?position_Navigation_small_navigation \<rightarrow> (SSTOP \<triangle> (set_position_Navigation_small_navigation\<^bold>!position_Navigation_small_navigation \<rightarrow> Skip)));; ((SSTOP \<triangle> (exit_Navigation_small_navigation \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_Navigation_small_navigation \<rightarrow> Skip);; (enter_CheckPosition_Navigation_small_navigation \<rightarrow> Trans_Navigation_small_navigation(NID_CheckPosition_Navigation_small_navigation)))))))))
                                         	  \<box>
                                         	  ((n = NID_CheckPosition_Navigation_small_navigation) \<^bold>& ((((position_Navigation_small_navigation \<le> target_Navigation_small_navigation)) \<^bold>& (((internal__Navigation_small_navigation\<^bold>.NID_CheckPosition_Navigation_small_navigation \<rightarrow> (SSTOP \<triangle> (proposal_out\<^bold>!1 \<rightarrow> Skip)));; (enter_WaitMoveApplied_Navigation_small_navigation \<rightarrow> Trans_Navigation_small_navigation(NID_WaitMoveApplied_Navigation_small_navigation))))))))
                                         	  \<box>
                                         	  ((n = NID_CheckPosition_Navigation_small_navigation) \<^bold>& ((((position_Navigation_small_navigation \<ge> target_Navigation_small_navigation)) \<^bold>& (((internal__Navigation_small_navigation\<^bold>.NID_CheckPosition_Navigation_small_navigation \<rightarrow> (SSTOP \<triangle> (proposal_out\<^bold>!0 \<rightarrow> Skip)));; (enter_WaitStopApplied_Navigation_small_navigation \<rightarrow> Trans_Navigation_small_navigation(NID_WaitStopApplied_Navigation_small_navigation))))))))
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

" Transc_Navigation_small_navigation(n) = 	((SSTOP \<triangle> (get_position_Navigation_small_navigation\<^bold>?position_Navigation_small_navigation \<rightarrow> (get_target_Navigation_small_navigation\<^bold>?target_Navigation_small_navigation \<rightarrow> (assume True (Transc_Navigation_small_navigation(n)) (((((((((n = NID_i0_Navigation_small_navigation) \<^bold>& (((internal__Navigation_small_navigation\<^bold>.NID_i0_Navigation_small_navigation \<rightarrow> Skip);; (enter_WaitTarget_Navigation_small_navigation \<rightarrow> Transc_Navigation_small_navigation(NID_WaitTarget_Navigation_small_navigation)))))
                                          	  \<box>
                                          	  ((n = NID_WaitTarget_Navigation_small_navigation) \<^bold>& (((setTarget__in\<^bold>.NID_WaitTarget_Navigation_small_navigation\<^bold>?target_Navigation_small_navigation \<rightarrow> (SSTOP \<triangle> (set_target_Navigation_small_navigation\<^bold>!target_Navigation_small_navigation \<rightarrow> Skip)));; ((SSTOP \<triangle> (exit_Navigation_small_navigation \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_Navigation_small_navigation \<rightarrow> Skip);; (enter_WaitForPose_Navigation_small_navigation \<rightarrow> Transc_Navigation_small_navigation(NID_WaitForPose_Navigation_small_navigation)))))))))
                                          	  \<box>
                                          	  ((n = NID_WaitForPose_Navigation_small_navigation) \<^bold>& (((globalpose__in\<^bold>.NID_WaitForPose_Navigation_small_navigation\<^bold>?position_Navigation_small_navigation \<rightarrow> (SSTOP \<triangle> (set_position_Navigation_small_navigation\<^bold>!position_Navigation_small_navigation \<rightarrow> Skip)));; ((SSTOP \<triangle> (exit_Navigation_small_navigation \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_Navigation_small_navigation \<rightarrow> Skip);; (enter_CheckPosition_Navigation_small_navigation \<rightarrow> Transc_Navigation_small_navigation(NID_CheckPosition_Navigation_small_navigation)))))))))
                                          	  \<box>
                                          	  ((n = NID_CheckPosition_Navigation_small_navigation) \<^bold>& ((((position_Navigation_small_navigation \<le> target_Navigation_small_navigation)) \<^bold>& (((internal__Navigation_small_navigation\<^bold>.NID_CheckPosition_Navigation_small_navigation \<rightarrow> (SSTOP \<triangle> (proposal_out\<^bold>!1 \<rightarrow> Skip)));; (enter_WaitMoveApplied_Navigation_small_navigation \<rightarrow> Transc_Navigation_small_navigation(NID_WaitMoveApplied_Navigation_small_navigation))))))))
                                          	  \<box>
                                          	  ((n = NID_CheckPosition_Navigation_small_navigation) \<^bold>& ((((position_Navigation_small_navigation \<ge> target_Navigation_small_navigation)) \<^bold>& (((internal__Navigation_small_navigation\<^bold>.NID_CheckPosition_Navigation_small_navigation \<rightarrow> (SSTOP \<triangle> (proposal_out\<^bold>!0 \<rightarrow> Skip)));; (enter_WaitStopApplied_Navigation_small_navigation \<rightarrow> Transc_Navigation_small_navigation(NID_WaitStopApplied_Navigation_small_navigation))))))))
                                          	  \<box>
                                          	  ((n = NID_WaitMoveApplied_Navigation_small_navigation) \<^bold>& (((OAApplied__in\<^bold>.NID_WaitMoveApplied_Navigation_small_navigation \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_Navigation_small_navigation \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_Navigation_small_navigation \<rightarrow> Skip);; (enter_WaitForPose_Navigation_small_navigation \<rightarrow> Transc_Navigation_small_navigation(NID_WaitForPose_Navigation_small_navigation)))))))))
                                          	  \<box>
                                          	  ((n = NID_WaitStopApplied_Navigation_small_navigation) \<^bold>& (((OAApplied__in\<^bold>.NID_WaitStopApplied_Navigation_small_navigation \<rightarrow> Skip);; ((SSTOP \<triangle> (exit_Navigation_small_navigation \<rightarrow> Skip));; (SSTOP \<triangle> ((exited_Navigation_small_navigation \<rightarrow> (SSTOP \<triangle> (targetReached_out \<rightarrow> Skip)));; (enter_f0_Navigation_small_navigation \<rightarrow> Transc_Navigation_small_navigation(NID_f0_Navigation_small_navigation)))))))))
                                          	  \<box>
                                          	  ((n = NID_f0_Navigation_small_navigation) \<^bold>& ((terminate \<rightarrow> Skip))))))))) " |

" ncCoreBehaviour_Navigation_small_navigation = 	((cRename (cCompleteRenaming (csbasic (share) \<times> csbasic (share))) ((cRename (cCompleteRenaming ((csbasic (interrupt_i0_Navigation_small_navigation) \<times> csbasic (internal__Navigation_small_navigation\<^bold>.NID_i0_Navigation_small_navigation)) \<union>
                                                   	 (csbasic (interrupt_WaitTarget_Navigation_small_navigation) \<times> csbasic (setTarget__in\<^bold>.NID_WaitTarget_Navigation_small_navigation)) \<union>
                                                   	 (csbasic (interrupt_WaitForPose_Navigation_small_navigation) \<times> csbasic (globalpose__in\<^bold>.NID_WaitForPose_Navigation_small_navigation)) \<union>
                                                   	 (csbasic (interrupt_CheckPosition_Navigation_small_navigation) \<times> csbasic (internal__Navigation_small_navigation\<^bold>.NID_CheckPosition_Navigation_small_navigation)) \<union>
                                                   	 (csbasic (interrupt_CheckPosition_Navigation_small_navigation) \<times> csbasic (internal__Navigation_small_navigation\<^bold>.NID_CheckPosition_Navigation_small_navigation)) \<union>
                                                   	 (csbasic (interrupt_WaitMoveApplied_Navigation_small_navigation) \<times> csbasic (OAApplied__in\<^bold>.NID_WaitMoveApplied_Navigation_small_navigation)) \<union>
                                                   	 (csbasic (interrupt_WaitStopApplied_Navigation_small_navigation) \<times> csbasic (OAApplied__in\<^bold>.NID_WaitStopApplied_Navigation_small_navigation)) \<union>
                                                   	 (csbasic (interrupt_f0_Navigation_small_navigation) \<times> csbasic (interrupt_Navigation_small_navigation)) \<union>
                                                   	 (csbasic (interrupt_WaitMoveApplied_Navigation_small_navigation) \<times> csbasic (interrupt_Navigation_small_navigation)) \<union>
                                                   	 (csbasic (interrupt_WaitTarget_Navigation_small_navigation) \<times> csbasic (interrupt_Navigation_small_navigation)) \<union>
                                                   	 (csbasic (interrupt_WaitForPose_Navigation_small_navigation) \<times> csbasic (interrupt_Navigation_small_navigation)) \<union>
                                                   	 (csbasic (interrupt_WaitStopApplied_Navigation_small_navigation) \<times> csbasic (interrupt_Navigation_small_navigation)))) (composeNodes_Navigation_small_navigation))))
                                                   	  \<lbrakk> \<^bold>0 | \<lbrace> exit_Navigation_small_navigation,enter_WaitForPose_Navigation_small_navigation,internal__Navigation_small_navigation\<^bold>.NID_i0_Navigation_small_navigation,internal__Navigation_small_navigation\<^bold>.NID_CheckPosition_Navigation_small_navigation,setTarget__in\<^bold>.NID_WaitTarget_Navigation_small_navigation,enter_f0_Navigation_small_navigation,globalpose__in\<^bold>.NID_WaitForPose_Navigation_small_navigation,OAApplied__in\<^bold>.NID_WaitMoveApplied_Navigation_small_navigation,interrupt_Navigation_small_navigation,enter_i0_Navigation_small_navigation,enter_WaitStopApplied_Navigation_small_navigation,OAApplied__in\<^bold>.NID_WaitStopApplied_Navigation_small_navigation,share,terminate,enter_WaitMoveApplied_Navigation_small_navigation,exited_Navigation_small_navigation,enter_WaitTarget_Navigation_small_navigation,enter_CheckPosition_Navigation_small_navigation \<rbrace> | \<^bold>0 \<rbrakk>
                                                   	  (cRename (cCompleteRenaming (csbasic (share) \<times> csbasic (share))) ((enter_i0_Navigation_small_navigation \<rightarrow> Trans_Navigation_small_navigation(NID_i0_Navigation_small_navigation))))) " |

" ncBehaviour_Navigation_small_navigation = 	(cRename (cCompleteRenaming project_triggers_Navigation_small_navigation) ((ncCoreBehaviour_Navigation_small_navigation \<Zhide> \<lbrace> enter_i0_Navigation_small_navigation,enter_WaitTarget_Navigation_small_navigation,enter_WaitForPose_Navigation_small_navigation,enter_CheckPosition_Navigation_small_navigation,enter_WaitMoveApplied_Navigation_small_navigation,enter_WaitStopApplied_Navigation_small_navigation,enter_f0_Navigation_small_navigation,exit_Navigation_small_navigation,exited_Navigation_small_navigation,internal__Navigation_small_navigation \<rbrace>))) " |

" machineBody_Navigation_small_navigation = 	((ncBehaviour_Navigation_small_navigation
                                            	  \<lbrakk> \<^bold>0 | \<lbrace> interrupt_Navigation_small_navigation \<rbrace> | \<^bold>0 \<rbrakk> 
                                            	  Skip) \<Zhide> enteredSS_in_stmbd_Navigation_small_navigation) " |

" Memory_target_Navigation_small_navigation(value) = 	(((get_target_Navigation_small_navigation\<^bold>!value \<rightarrow> Memory_target_Navigation_small_navigation(value))
                                                     	  \<box>
                                                     	  ((set_target_Navigation_small_navigation\<^bold>?x__v \<rightarrow> Memory_target_Navigation_small_navigation(x__v))
                                                     	  \<box>
                                                     	  (terminate \<rightarrow> Skip)))) " |

" Memory_position_Navigation_small_navigation(value) = 	(((get_position_Navigation_small_navigation\<^bold>!value \<rightarrow> Memory_position_Navigation_small_navigation(value))
                                                       	  \<box>
                                                       	  ((set_position_Navigation_small_navigation\<^bold>?x__v \<rightarrow> Memory_position_Navigation_small_navigation(x__v))
                                                       	  \<box>
                                                       	  (terminate \<rightarrow> Skip)))) " |

" varMemory_Navigation_small_navigation = 	(Memory_target_Navigation_small_navigation((0::nat))
                                          	  \<lbrakk> \<^bold>0 | \<lbrace> terminate \<rbrace> | \<^bold>0 \<rbrakk> 
                                             	  Memory_position_Navigation_small_navigation((0::nat))) " |

" stateful_Navigation_small_navigation = 	((machineBody_Navigation_small_navigation
                                            	  \<lbrakk> \<^bold>0 | \<lbrace> get_position_Navigation_small_navigation,get_target_Navigation_small_navigation,terminate,set_position_Navigation_small_navigation,set_target_Navigation_small_navigation \<rbrace> | \<^bold>0 \<rbrakk>
                                            	  varMemory_Navigation_small_navigation) \<Zhide> \<lbrace> get_position_Navigation_small_navigation,get_target_Navigation_small_navigation,set_position_Navigation_small_navigation,set_target_Navigation_small_navigation \<rbrace>) " |

" sharedVarMemory_Navigation_small_navigation = 	(terminate \<rightarrow> Skip) " |

" stm_Navigation_small_navigation = 	((((cRename (cCompleteRenaming ({})) (((stateful_Navigation_small_navigation \<Zhide> \<lbrace> terminate \<rbrace>);; (SSTOP \<triangle> (terminate \<rightarrow> Skip)))))
                                       	  \<lbrakk> \<^bold>0 | shared_variable_events_in_stmbd_Navigation_small_navigation | \<^bold>0 \<rbrakk>
                                       	  Skip)
                                       	  \<lbrakk> \<^bold>0 | \<lbrace> terminate \<rbrace> | \<^bold>0 \<rbrakk>
                                       	  sharedVarMemory_Navigation_small_navigation) \<Zhide> ({} :: mychan set)) "

definition Small_Navigation :: "(mychan, unit) cyphyaction" where
  "Small_Navigation = stm_Navigation_small_navigation"

setup \<open>Sign.parent_path\<close>

end
