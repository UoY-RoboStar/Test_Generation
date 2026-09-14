theory TestGen
  imports Axiomatic_CyPhyCircus.Ax_CyPhyCircus Codegen
  keywords "generate_tests_rct" :: thy_decl
    and "RoboChart" "Mutants" "RoboWorld" "Iterations"
begin

named_theorems rct_defs (* define a theorem set for process definitions so unfolding can be done easier *)

method rct_refine = (simp?, unfold rct_defs, rule ref_preorder.order_refl)
method rct_refine_by_trace = fail
method rct_simp_counterexample =
  (unfold cyphycircus_trace_ref_by_def recursive_defs rec_sys_defs rct_defs, safe)

ML \<open>exnMessage\<close>

ML \<open>fun obtainCounterexample' ctxt (spec : term) (impl : term) () =
      let val spec_type = Term.fastype_of spec
          val type_error = TYPE ("type of specification and implementation must be cyphyaction:",[spec_type],[spec, impl])
          val (evT, stT) =
            case dest_Type spec_type of
                (ty_name, evT :: stT :: _) =>
                  if ty_name = @{type_name "cyphyaction"} then (evT, stT) else raise type_error
              | _ => raise type_error
          val recursive_defs = Named_Theorems.get ctxt @{named_theorems recursive_defs}
          val rec_sys_defs = Named_Theorems.get ctxt @{named_theorems rec_sys_defs}
          val cyphyaction_datatype_unfolds = Named_Theorems.get ctxt @{named_theorems cyphyaction_datatype_unfolds}
          val unfolds = recursive_defs @ rec_sys_defs @ cyphyaction_datatype_unfolds
          val spec = Raw_Simplifier.rewrite_term (Proof_Context.theory_of ctxt) unfolds [] spec
          val impl = Raw_Simplifier.rewrite_term (Proof_Context.theory_of ctxt) unfolds [] impl
          val check_result_no_tick = 
            check_cyphycircus_trace_incremental_ref_by ctxt stT evT
              50(*breadth*) 10(*depth*) 1000(*step limit*) 100(*timestep denominator*) false spec impl
      in
        case check_result_no_tick of
            Exn.Res (SOME terms) => SOME terms
          | Exn.Res NONE => NONE
          | Exn.Exn e => (warning (exnMessage e); NONE)
      end\<close>

ML \<open>fun obtainCounterexample ctxt (spec : term) (impl : term) = 
      Timeout.apply (Time.fromSeconds 3) (obtainCounterexample' ctxt spec impl) ()
      handle Timeout.TIMEOUT _ => (warning "checking timed out"; NONE)\<close>

ML \<open>fun term_to_name ctxt term =
      let val text = XML.content_of (YXML.parse_body (Syntax.string_of_term ctxt term))
          val ident_tokens = String.tokens (not o Symbol.is_letdig o str) text
      in
        if Symbol_Pos.is_identifier text then 
          text 
        else
          (if null ident_tokens then "term" else (hd ident_tokens) ^ "_") ^ (SHA1.rep (SHA1.digest text))
      end\<close>
          
ML \<open>fun checkRefinement ctxt (spec : term) (impl : term) =
      let val spec_type = Term.fastype_of spec
          val ref_by = Const (@{const_name ref_by}, spec_type --> spec_type --> @{typ bool})
          val statement = Thm.cterm_of ctxt (HOLogic.mk_Trueprop (ref_by $ spec $ impl))
          val goal = Goal.init statement
          val rct_refine = Method.method ctxt (Token.make_src (@{method rct_refine}, Position.start) [])
          val goal_seq = rct_refine ctxt [] (ctxt, goal)
      in case Seq.pull goal_seq of
            NONE =>
              (* proof method failed, try to construct counterexample *)
              (SOME (obtainCounterexample ctxt spec impl), ctxt)
          | SOME (Seq.Result (ctxt, goal), _) =>
              (* proof method succeeded, do we have a finished goal? *)
              if Thm.no_prems goal then
                (* This looks like a finished goal, convert it to a finished theorem and save it *)
                let val finished_goal = Goal.finish ctxt goal
                    val impl_ident = term_to_name ctxt impl
                    val spec_ident = term_to_name ctxt spec
                    val name = impl_ident ^ "_refines_" ^ spec_ident
                    val binding = Binding.name name
                    val ((bound_name, _), ctxt) = Local_Theory.note ((binding, []), [finished_goal]) ctxt
                in (NONE, ctxt) end
              else
                (* proof method didn't finish the proof, try to construct counterexample *)
                (SOME (obtainCounterexample ctxt spec impl), ctxt)
          | SOME (Seq.Error err, _) =>
              (* an error occurred, report it and try to construct counterexample *)
              let val _ = warning (err ())
              in (SOME (obtainCounterexample ctxt spec impl), ctxt)
              end
      end
\<close>

ML \<open>fun checkTraceOf ctxt (impl : term) (trace : term list)  = (NONE, ctxt)\<close>

ML \<open>fun traceToProcess typ (trace : term list) =
          if null trace then
            Const (@{const_name Skip}, typ)
          else 
            let val evt_typ = fastype_of (hd trace)
            in Const (@{const_name SyncPrefix}, evt_typ --> typ --> typ) $ (hd trace) $ traceToProcess typ (tl trace)
            end\<close>

ML \<open>structure TraceSet = Set(type key = term list val ord = list_ord Term_Ord.fast_term_ord)\<close>
ML \<open>structure TermSet = Set(type key = term val ord = Term_Ord.fast_term_ord)\<close>

ML \<open>fun testGeneration ctxt rct muts rwd n = 
      let val rctType = fastype_of rct
          fun testGenLoop ctxt mutsToCheck refiningMuts failedMuts feasibleTrs infeasibleTrs n =
            let val tracesThenAny =
                      map (fn trace => Const (@{const_name useq}, rctType --> rctType --> rctType) $ traceToProcess rctType trace $
                        Const (@{const_name cChaos}, rctType)) (TraceSet.dest (infeasibleTrs))
                val infeasibleProcess = Const (@{const_name Sup}, (HOLogic.mk_setT rctType) --> rctType) $ (HOLogic.mk_set rctType tracesThenAny)
                val robochartPlusTraces = 
                  if null tracesThenAny then
                    rct
                  else
                    Const (@{const_name "sup"}, rctType --> rctType --> rctType) $ rct $ infeasibleProcess
                fun checkMutant mut (refMuts, failMuts, traces, ctxt) = 
                  case checkRefinement ctxt robochartPlusTraces mut of
                      (NONE, ctxt) => (
                        (*writeln ("refining mutant: " ^ (Syntax.string_of_term ctxt mut));*)
                        (TermSet.insert mut refMuts, failedMuts, traces, ctxt))
                    | (SOME NONE, ctxt) => (
                        (*writeln ("failed mutant: " ^ (Syntax.string_of_term ctxt mut));*)
                        (refMuts, TermSet.insert mut failedMuts, traces, ctxt))
                    | (SOME (SOME trace), ctxt) => (
                        (*writeln ("trace generated: " ^ (String.concatWith " \<rightarrow> " (map (Pretty.pure_string_of o Syntax.pretty_term ctxt) trace)));*)
                        (refMuts, failedMuts, TraceSet.insert trace traces, ctxt))
                val (refMuts, failMuts, traces, ctxt) =
                      TermSet.fold checkMutant mutsToCheck (refiningMuts, failedMuts, TraceSet.empty, ctxt)
                fun checkTrace trace (fts, its, ctxt) =
                  case checkTraceOf ctxt rwd trace of
                      (NONE, ctxt) => (
                        (*writeln ("feasible trace: " ^ (String.concatWith " \<rightarrow> " (map (Pretty.pure_string_of o Syntax.pretty_term ctxt) trace)));*)
                        (TraceSet.insert trace fts, its, ctxt))
                    | (SOME counterexamplePrefix, ctxt) => (
                        (*writeln ("infeasible trace counterexample: " ^ (String.concatWith " \<rightarrow> " (map (Pretty.pure_string_of o Syntax.pretty_term ctxt) counterexamplePrefix)));*)
                        (fts, TraceSet.insert counterexamplePrefix its, ctxt))
                val (fts, its, ctxt) = TraceSet.fold checkTrace traces (feasibleTrs, infeasibleTrs, ctxt)
                val newMutsToCheck = TermSet.subtract failMuts (TermSet.subtract refMuts mutsToCheck)
            in if n > 1 then testGenLoop ctxt newMutsToCheck refMuts failMuts fts its (n-1) else (refMuts, failMuts, fts, its, ctxt)
            end
          val (refMuts, failMuts, fts, its, ctxt) =
            testGenLoop ctxt (TermSet.make muts) TermSet.empty TermSet.empty TraceSet.empty TraceSet.empty n
          val term_string = Pretty.pure_string_of o Syntax.pretty_term ctxt
          fun traceToString trace = String.concatWith " \<rightarrow> " (map term_string trace)
      in
        writeln "Feasible Traces Generated:";
        map (fn trace => (writeln ("  " ^ (traceToString trace)))) (TraceSet.dest fts);
        writeln "Refining mutants:";
        map (fn t => (writeln ("  " ^ (term_string t)))) (TermSet.dest refMuts);
        ctxt
      end\<close>

ML \<open>Outer_Syntax.local_theory \<^command_keyword>\<open>generate_tests_rct\<close>
  "generates tests from the semantics of a RoboChart model and its mutants, incorporating a RoboWorld model"
  ((((Parse.$$$ "RoboChart" -- Parse.$$$ "=")  |-- Parse.term)
    -- ((Parse.$$$ "Mutants" -- Parse.$$$ "=")  |-- Parse.list1 Parse.term)
    -- ((Parse.$$$ "RoboWorld" -- Parse.$$$ "=")  |-- Parse.term)
    -- ((Parse.$$$ "Iterations" -- Parse.$$$ "=")  |-- Parse.nat))
  >> (fn (((rct, muts), rwd), n) => fn ctxt =>
      let val rct_term = Syntax.read_term ctxt rct
          val mut_terms = map (Syntax.read_term ctxt) muts
          val rwd_term = Syntax.read_term ctxt rwd
      in testGeneration ctxt rct_term mut_terms rwd_term n
      end))\<close>

end