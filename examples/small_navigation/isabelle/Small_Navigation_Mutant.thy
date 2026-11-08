theory Small_Navigation_Mutant
  imports Small_Navigation
begin

text \<open>The mutant repeats only the process definitions of the nominal model. The channel sets
  and the renaming relation used by those definitions are those of the nominal model; its
  remaining constants are hidden so that the definitions can declare them again.\<close>

setup \<open>fn thy =>
  let
    val shared = map (prefix "Small_Navigation.Navigation.")
      ["enteredSS_in_stmbd_Navigation_small_navigation",
       "shared_variable_events_in_stmbd_Navigation_small_navigation",
       "renameTriggerEvents_Navigation_small_navigation"]
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
(* The processes follow the Ranger example (Ax_CyPhyCircus examples/Ranger_CyPhyCircus.thy): each group of
   mutually recursive processes is one recursive block, and the blocks and definitions appear in
   dependency order.
   The equations are those of Small_Navigation.thy with position < target changed to position \<le> target. *)

(* SSTOP is defined as an lfp directly, since recursive cannot unfold a block that refers to
   a process from an earlier recursive block. SSTOP_unfold restates the original equation. *)
definition SSTOP :: "(mychan, unit) cyphyaction" where
"SSTOP = (\<nu> X. share \<rightarrow> X)"

lemma SSTOP_unfold: "SSTOP = share  \<rightarrow>  SSTOP"
  unfolding SSTOP_def by (rule lfp_unfold, rule monoI, rule cSync_mono, assumption)

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

recursive
  Trans_Navigation_small_navigation :: "NIDS_Navigation_small_navigation \<Rightarrow> (mychan, unit) cyphyaction"
where
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
                                            	  (terminate \<rightarrow> Skip)))))))) "

recursive
  Transc_Navigation_small_navigation :: "NIDS_Navigation_small_navigation \<Rightarrow> (mychan, unit) cyphyaction"
where
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
                                             	  ((n = NID_f0_Navigation_small_navigation) \<^bold>& ((terminate \<rightarrow> Skip))))))))) "

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

definition ncBehaviour_Navigation_small_navigation :: "(mychan, unit) cyphyaction" where
" ncBehaviour_Navigation_small_navigation = 	(cRename renameTriggerEvents_Navigation_small_navigation ((ncCoreBehaviour_Navigation_small_navigation \<Zhide> \<lbrace> enter_i0_Navigation_small_navigation,enter_WaitTarget_Navigation_small_navigation,enter_WaitForPose_Navigation_small_navigation,enter_CheckPosition_Navigation_small_navigation,enter_WaitMoveApplied_Navigation_small_navigation,enter_WaitStopApplied_Navigation_small_navigation,enter_f0_Navigation_small_navigation,exit_Navigation_small_navigation,exited_Navigation_small_navigation,internal__Navigation_small_navigation \<rbrace>))) "

definition machineBody_Navigation_small_navigation :: "(mychan, unit) cyphyaction" where
" machineBody_Navigation_small_navigation = 	((ncBehaviour_Navigation_small_navigation
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

definition stm_Navigation_small_navigation :: "(mychan, unit) cyphyaction" where
" stm_Navigation_small_navigation = 	((((cRename ({} :: mychan \<leftrightarrow> mychan) (((stateful_Navigation_small_navigation \<Zhide> \<lbrace> terminate \<rbrace>);; (SSTOP \<triangle> (terminate \<rightarrow> Skip)))))
                                       	  \<lbrakk> \<^bold>0 | shared_variable_events_in_stmbd_Navigation_small_navigation | \<^bold>0 \<rbrakk>
                                       	  Skip)
                                       	  \<lbrakk> \<^bold>0 | \<lbrace> terminate \<rbrace> | \<^bold>0 \<rbrakk>
                                       	  sharedVarMemory_Navigation_small_navigation) \<Zhide> ({} :: mychan set)) "

definition Small_Navigation :: "(mychan, unit) cyphyaction" where
  "Small_Navigation = stm_Navigation_small_navigation"

setup \<open>Sign.parent_path\<close>

end
