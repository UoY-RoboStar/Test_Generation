theory TestGen
  imports CyPhy_CodeGen
  keywords "generate_tests_rct" :: thy_decl
    and "RoboChart" "Mutants" "RoboWorld" "Iterations"
begin

named_theorems rct_defs (* define a theorem set for process definitions so unfolding can be done easier *)
named_theorems cyphy_model_unfolding
  \<open>equations unfolded before CSP step-law normalisation\<close>

method rct_refine =
  (simp only: rct_defs cyphy_model_unfolding ax_step_laws chan_defs
     ax_cSync_chinst1_event_prefix evsimple_chinst1
     ctor_prism_def chinst1_def evsimple_def
     ref_by_cyphyaction_def order_refl)
method rct_refine_by_trace = fail
method rct_simp_counterexample = clarsimp

ML \<open>
structure CyPhy_CheckRefinement =
struct

type normalised_processes =
  {spec: term,
   impl: term}

datatype verdict =
    ProvedRefines
  | Normalised of normalised_processes

fun normalised_residual remaining =
  (case Thm.prems_of remaining of
    [goal] =>
      let
        val body = goal |> Logic.strip_assums_concl |> HOLogic.dest_Trueprop
      in
        (case body of
          Const (name, _) $ left $ right =>
            if name = \<^const_name>\<open>ref_by\<close>
            then (left, right)
            else if name = \<^const_name>\<open>less_eq\<close>
            then (right, left)
            else raise TERM
              ("rct_refine residual is not a refinement relation", [body])
        | _ => raise TERM
            ("rct_refine residual is not a binary refinement relation", [body]))
      end
  | goals => raise TERM
      ("rct_refine must leave exactly one residual goal", goals))

end
\<close>


ML \<open>
val testgen_loop_depth =
  Attrib.setup_config_int \<^binding>\<open>testgen_loop_depth\<close> (K 12)
val testgen_trace_depth =
  Attrib.setup_config_int \<^binding>\<open>testgen_trace_depth\<close> (K 8)
val testgen_quickcheck_timeout =
  Attrib.setup_config_real \<^binding>\<open>testgen_quickcheck_timeout\<close> (K 30.0)

fun quickcheck_counterexample ctxt spec_code impl_code =
  let
    val codeT = Term.fastype_of spec_code
    val eventT =
      (case codeT of
        Type (name, [T]) =>
          if name = \<^type_name>\<open>cyphy_code\<close> then T
          else raise TYPE ("cyphy_code expected", [codeT], [])
      | _ => raise TYPE ("cyphy_code expected", [codeT], []))
    val _ =
      if Term.fastype_of impl_code = codeT then ()
      else raise TYPE
        ("specification and implementation code types differ",
          [codeT, Term.fastype_of impl_code], [])
    val traceT = HOLogic.listT eventT
    val trace = Free ("trace", traceT)
    val property =
      HOLogic.mk_Trueprop
        (Const (\<^const_name>\<open>bounded_trace_inclusion\<close>,
           \<^typ>\<open>nat\<close> --> \<^typ>\<open>nat\<close> -->
             codeT --> codeT --> traceT --> \<^typ>\<open>bool\<close>) $
         HOLogic.mk_nat (Config.get ctxt testgen_loop_depth) $
         HOLogic.mk_nat (Config.get ctxt testgen_trace_depth) $
         spec_code $ impl_code $ trace)
    val qc_ctxt =
      ctxt
      |> Config.put Quickcheck.size (Config.get ctxt testgen_trace_depth)
      |> Config.put Quickcheck.timeout (Config.get ctxt testgen_quickcheck_timeout)
      |> Config.put Quickcheck.quiet true
      |> Context.proof_map (Quickcheck.set_active_testers ["exhaustive"])
    val counterexample =
      (case Quickcheck.test_terms qc_ctxt (true, true) [] [(property, [])] of
        NONE => NONE
      | SOME results => get_first Quickcheck.counterexample_of results)
    fun trace_of assignments =
      get_first
        (fn (_, value) =>
          if Term.fastype_of value = traceT then SOME value else NONE)
        assignments
  in
    (case counterexample of
      SOME (true, assignments) =>
        Option.map (HOLogic.dest_list) (trace_of assignments)
    | _ => NONE)
  end

fun obtainCounterexample ctxt
      ({spec, impl}: CyPhy_CheckRefinement.normalised_processes) =
  let
    val spec_code = CyPhy_CodeGen.codegen_normalised ctxt spec
    val impl_code = CyPhy_CodeGen.codegen_normalised ctxt impl
  in
    (quickcheck_counterexample ctxt spec_code impl_code, ctxt)
  end
\<close>

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
          val goal = Goal.init  statement
          val rct_refine = Method.method ctxt (Token.make_src (@{method rct_refine}, Position.start) [])
          val goal_seq = rct_refine ctxt [] (ctxt, goal)
      in case Seq.pull goal_seq of
            NONE => error "rct_refine returned no result"
          | SOME (Seq.Result (ctxt, goal), _) => (* proof method succeeded, do we have a finished goal? *)
              if Thm.no_prems goal then
                (* This looks like a finished goal, convert it to a finished theorem and save it *)
                let val finished_goal = Goal.finish ctxt goal
                    val impl_ident = term_to_name ctxt impl
                    val spec_ident = term_to_name ctxt spec
                    val name = impl_ident ^ "_refines_" ^ spec_ident
                    val binding = Binding.name name
                    val ((bound_name, _), ctxt) = Local_Theory.note ((binding, []), [finished_goal]) ctxt
                in (CyPhy_CheckRefinement.ProvedRefines, ctxt) end
              else (* proof method didn't finish the proof, retain its normalised operands *)
                let val (normalised_spec, normalised_impl) =
                      CyPhy_CheckRefinement.normalised_residual goal
                in (CyPhy_CheckRefinement.Normalised
                      {spec = normalised_spec, impl = normalised_impl}, ctxt) end
          | SOME (Seq.Error err, _) =>
              error (err ())
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
                      (CyPhy_CheckRefinement.ProvedRefines, ctxt) => (
                        (*writeln ("refining mutant: " ^ (Syntax.string_of_term ctxt mut));*)
                        (TermSet.insert mut refMuts, failedMuts, traces, ctxt))
                    | (CyPhy_CheckRefinement.Normalised stage, ctxt) =>
                        (case obtainCounterexample ctxt stage of
                          (SOME trace, ctxt) => (
                            (*writeln ("trace generated: " ^ (Pretty.pure_string_of (Syntax.pretty_term ctxt trace)));*)
                            (refMuts, failedMuts, TraceSet.insert trace traces, ctxt))
                        | (NONE, ctxt) => (
                            (*writeln ("failed mutant: " ^ (Syntax.string_of_term ctxt mut));*)
                            (refMuts, TermSet.insert mut failedMuts, traces, ctxt))
                        )
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
