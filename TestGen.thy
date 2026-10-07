theory TestGen
  imports Ax_CyPhyCircus Codegen tactics
  keywords "generate_tests_rct" :: thy_decl
    and "RoboChart" "Mutants" "RoboWorld" "Iterations"
begin

section \<open>Declare options for the test generation algorithm\<close>

ML \<open>fun code_real_of_rat n d = @{term code_real_of_rat} $ (HOLogic.mk_nat n) $ (HOLogic.mk_nat d)\<close>
ML \<open>fun parse_rat_term str =
      if String.member str #"/" then
        case String.tokens (equal #"/") str of
            [num, den] =>
              (case (Int.fromString num, Int.fromString den) of
                  (SOME num, SOME den) => SOME (@{term code_real_of_rat} $ (HOLogic.mk_nat num) $ (HOLogic.mk_nat den))
                | _ => NONE)
            | _ => NONE
      else if String.member str #"." then
        case String.tokens (equal #".") (if String.isPrefix "." str andalso not (String.isSuffix "." str) then "0"^str else str) of
            [int, frac] =>
              let val int = if String.size int = 0 then SOME 0 else Int.fromString int 
                  val int = Option.map (fn x => code_real_of_rat x 1) int
                  val frac_den = String.size frac
                  val frac = if frac_den = 0 then 
                      SOME (code_real_of_rat 0 1)
                    else
                      Option.map (fn x => code_real_of_rat x (Integer.pow frac_den 10)) (Int.fromString frac)
              in (case (int, frac) of
                      (SOME int, SOME frac) => SOME (@{term "plus :: real \<Rightarrow> real \<Rightarrow> real"} $ int $ frac)
                    | _ => NONE)
              end
          | [int] => Option.map (fn x => code_real_of_rat x 1) (Int.fromString int)
          | _ => NONE
      else
        Option.map (fn x => code_real_of_rat x 1) (Int.fromString str)\<close>


text \<open>testgen_step_limit: limit on the number of non-event steps searched through before assuming divergence\<close>
ML \<open>val testgen_step_limit_opt = Attrib.setup_config_int @{binding testgen_step_limit} (K 1000)\<close>
ML \<open>fun set_testgen_step_limit_opt value pos ctxt =
      case Int.fromString value of
          SOME n => Config.put testgen_step_limit_opt n ctxt
        | NONE => error ("testgen_step_limit must be a positive integer" ^ Position.here pos)\<close>
ML \<open>fun get_testgen_step_limit_opt ctxt = Config.get ctxt testgen_step_limit_opt\<close>

text \<open>testgen_timestep: time step used to process continuous evolutions\<close>
ML \<open>val testgen_timestep_opt = Attrib.setup_config_string @{binding testgen_timestep} (K "1/100")\<close>
ML \<open>fun set_testgen_timestep_opt value pos ctxt =
      case parse_rat_term value of
          SOME _ => Config.put testgen_timestep_opt value ctxt
        | NONE => error ("testgen_timestep must be a string representing a valid rational number" ^ Position.here pos)\<close>
ML \<open>fun get_testgen_timestep_opt ctxt = the (parse_rat_term (Config.get ctxt testgen_timestep_opt))\<close>

text \<open>testgen_trace_depth: length of traces searched for\<close>
ML \<open>val testgen_trace_depth_opt = Attrib.setup_config_int @{binding testgen_trace_depth} (K 10)\<close>
ML \<open>fun set_testgen_trace_depth_opt value pos ctxt =
      case Int.fromString value of
          SOME n => Config.put testgen_trace_depth_opt n ctxt
        | NONE => error ("testgen_trace_depth must be a positive integer" ^ Position.here pos)\<close>
ML \<open>fun get_testgen_trace_depth_opt ctxt = Config.get ctxt testgen_trace_depth_opt\<close>

text \<open>testgen_trace_breadth: bound on the breadth of channel events to be searched when constructing traces\<close>
ML \<open>val testgen_trace_breadth_opt = Attrib.setup_config_int @{binding testgen_trace_breadth} (K 30)\<close>
ML \<open>fun set_testgen_trace_breadth_opt value pos ctxt =
      case Int.fromString value of
          SOME n => Config.put testgen_trace_breadth_opt n ctxt
        | NONE => error ("testgen_trace_breadth must be a positive integer" ^ Position.here pos)\<close>
ML \<open>fun get_testgen_trace_breadth_opt ctxt = Config.get ctxt testgen_trace_breadth_opt\<close>

text \<open>testgen_consts_breadth: bound on the breadth of values to be searched when testing constant instantiations\<close>
ML \<open>val testgen_consts_breadth_opt = Attrib.setup_config_int @{binding testgen_consts_breadth} (K 50)\<close>
ML \<open>fun set_testgen_consts_breadth_opt value pos ctxt =
      case Int.fromString value of
          SOME n => Config.put testgen_consts_breadth_opt n ctxt
        | NONE => error ("testgen_consts_breadth must be a positive integer" ^ Position.here pos)\<close>
ML \<open>fun get_testgen_consts_breadth_opt ctxt = Config.get ctxt testgen_consts_breadth_opt\<close>

text \<open>testgen_timeout: time in milliseconds to wait for checks to return a trace\<close>
ML \<open>val testgen_timeout_opt = Attrib.setup_config_int @{binding testgen_timeout} (K 3000)\<close>
ML \<open>fun set_testgen_timeout_opt value pos ctxt =
      case Int.fromString value of
          SOME n => Config.put testgen_timeout_opt n ctxt
        | NONE => error ("testgen_timeout must be a positive integer" ^ Position.here pos)\<close>
ML \<open>fun get_testgen_timeout_opt ctxt = Config.get ctxt testgen_timeout_opt\<close>

text \<open>testgen_verbose: whether to produce additional debug output\<close>
ML \<open>val testgen_verbose_opt = Attrib.setup_config_bool @{binding testgen_verbose} (K false)\<close>
ML \<open>fun set_testgen_verbose_opt value pos ctxt =
      case Bool.fromString value of
          SOME n => Config.put testgen_verbose_opt n ctxt
        | NONE => error ("testgen_verbose must be a boolean value" ^ Position.here pos)\<close>
ML \<open>fun get_testgen_verbose_opt ctxt = Config.get ctxt testgen_verbose_opt\<close>

ML \<open>fun parse_testgen_opts ctxt opts = fold (fn ((name, name_pos), (value, value_pos)) => fn ctxt =>
      case name of
        "testgen_step_limit" => set_testgen_step_limit_opt value value_pos ctxt
      | "testgen_timestep" => set_testgen_timestep_opt value value_pos ctxt
      | "testgen_trace_depth" => set_testgen_trace_depth_opt value value_pos ctxt
      | "testgen_trace_breadth" => set_testgen_trace_breadth_opt value value_pos ctxt
      | "testgen_consts_breadth" => set_testgen_consts_breadth_opt value value_pos ctxt
      | "testgen_timeout" => set_testgen_timeout_opt value value_pos ctxt
      | "testgen_verbose" => set_testgen_verbose_opt value value_pos ctxt
      | _ => error ("unknown option: " ^ name ^ (Position.here name_pos))) opts ctxt\<close>


section \<open>Proof methods for use by the test generation algorithm\<close>

text \<open>rct_defs and rct_refine are defined in tactics.\<close>

method rct_refine_by_trace = fail
method rct_simp_counterexample =
  (simp add: recursive_defs rec_sys_defs rct_defs)

section \<open>Construction of counterexamples\<close>

lemma search_event_prefix_function [cyphy_search_preparation]:
  "cEventPrefix e = cOutputPrefix' (\<lambda>_. e)"
  by (rule ext)
     (simp only: event_prefix_as_output cOutputPrefix_cOutputPrefix' prism_id_def
       refinement_prism_build comp_def id_apply)

ML \<open>
  fun prepareCounterexample ctxt process =
    let
      val equations = Named_Theorems.get ctxt @{named_theorems recursive_defs} @
        Named_Theorems.get ctxt @{named_theorems rec_sys_defs} @
        Named_Theorems.get ctxt @{named_theorems cyphy_search_preparation} @
        Named_Theorems.get ctxt @{named_theorems cyphyaction_datatype_unfolds}
      val ctxt' = put_simpset HOL_basic_ss ctxt addsimps equations
      val equality = Simplifier.rewrite ctxt' (Thm.cterm_of ctxt process)
    in (Thm.term_of (Thm.rhs_of equality), equality) end
\<close>

ML \<open>fun obtainCounterexample' ctxt (spec : term) (impl : term) () =
      let val spec_type = Term.fastype_of spec
          val type_error = TYPE ("type of specification and implementation must be cyphyaction:",[spec_type],[spec, impl])
          val (evT, stT) =
            case dest_Type spec_type of
                (ty_name, evT :: stT :: _) =>
                  if ty_name = @{type_name "cyphyaction"} then (evT, stT) else raise type_error
              | _ => raise type_error
          val ref_by = Const (@{const_name ref_by}, spec_type --> spec_type --> @{typ bool})
          val statement = Thm.cterm_of ctxt (HOLogic.mk_Trueprop (ref_by $ spec $ impl))
          val goal = Goal.init statement
          val rct_simp_counterexample = Method.method ctxt (Token.make_src (@{method rct_simp_counterexample}, Position.none) [])
          val goal_seq = rct_simp_counterexample ctxt [] (ctxt, goal)
          val (spec, impl) =
                case Seq.pull goal_seq of
                    NONE =>
                      (* proof method failed, try to construct counterexample with unsimplified spec and impl *)
                      (spec, impl)
                  | SOME (Seq.Result (_, goal), _) =>
                      (* proof method succeeded, unpack new spec and impl *)
                      (case Thm.prems_of goal of
                          [] => (spec, impl)
                        | subgoal::_ => 
                            (case strip_comb (HOLogic.dest_Trueprop subgoal) of
                                (Const (@{const_name ref_by}, _), [spec, impl]) => (spec, impl)
                              | _ => (spec, impl)))
                  | SOME (Seq.Error err, _) =>
                      (* an error occurred, report it and try to construct counterexample with unsimplified spec and impl *)
                      let val _ = warning (err ())
                      in (spec, impl)
                      end
          val trace_breadth = get_testgen_trace_breadth_opt ctxt
          val trace_depth = get_testgen_trace_depth_opt ctxt
          val step_limit = get_testgen_step_limit_opt ctxt
          val timestep = get_testgen_timestep_opt ctxt
          val check_result_no_tick = 
            check_cyphycircus_trace_incremental_ref_by_no_hiding ctxt stT evT
              trace_breadth trace_depth step_limit timestep false spec impl
      in
        case check_result_no_tick of
            Exn.Res (SOME terms) => SOME terms
          | Exn.Res NONE => NONE
          | Exn.Exn e => (warning (exnMessage e); NONE)
      end\<close>

ML \<open>fun obtainCounterexample ctxt (spec : term) (impl : term) = 
      Timeout.apply (Time.fromMilliseconds (get_testgen_timeout_opt ctxt)) (obtainCounterexample' ctxt spec impl) ()
      handle Timeout.TIMEOUT _ => (warning "checking timed out"; NONE)\<close>


section \<open>Refinement checking\<close>

ML \<open>fun term_to_name ctxt term =
      let val text = XML.content_of (YXML.parse_body (Syntax.string_of_term ctxt term))
          val ident_tokens = String.tokens (not o Symbol.is_letdig o str) text
      in
        if Symbol_Pos.is_identifier text then 
          text 
        else
          (if null ident_tokens then "term" else (hd ident_tokens) ^ "_") ^ (SHA1.rep (SHA1.digest text))
      end\<close>
          
(* Returns the specification and implementation from the goal that rct_refine leaves,
   which has the form impl <= spec or ref_by spec impl. *)
ML \<open>fun simplifiedOperands goal =
      case HOLogic.dest_Trueprop (Logic.strip_assums_concl (hd (Thm.prems_of goal))) of
          Const (@{const_name less_eq}, _) $ impl $ spec => (spec, impl)
        | Const (@{const_name ref_by}, _) $ spec $ impl => (spec, impl)\<close>

ML \<open>fun checkRefinement ctxt (spec : term) (impl : term) =
      let val spec_type = Term.fastype_of spec
          val ref_by = Const (@{const_name ref_by}, spec_type --> spec_type --> @{typ bool})
          val statement = Thm.cterm_of ctxt (HOLogic.mk_Trueprop (ref_by $ spec $ impl))
          val goal = Goal.init statement
          val rct_refine = Method.method ctxt (Token.make_src (@{method rct_refine}, Position.none) [])
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
                (* proof method didn't finish the proof, try to construct counterexample
                   from the simplified specification and implementation *)
                let val (spec, impl) = simplifiedOperands goal
                in (SOME (obtainCounterexample ctxt spec impl), ctxt) end
          | SOME (Seq.Error err, _) =>
              (* an error occurred, report it and try to construct counterexample *)
              let val _ = warning (err ())
              in (SOME (obtainCounterexample ctxt spec impl), ctxt)
              end
      end
\<close>

section \<open>Trace checking\<close>

ML \<open>fun checkTraceOf' ctxt (rwd : term) (rwd_pred : term) (trace : term list) () = 
      let val rwd_type = Term.fastype_of rwd
          val rwd_type_error = TYPE ("type of RoboWorld process must be a (single-argument) function that outputs cyphyaction:",[rwd_type],[rwd])
          val (inpT, evT, stT) =
            case dest_Type rwd_type of
                (@{type_name "fun"}, [inp, outp]) =>
                  (case dest_Type outp of
                      (@{type_name "cyphyaction"}, [evT, stT]) => (inp, evT, stT)
                    | _ => raise rwd_type_error)
              | _ => raise rwd_type_error
          val rwd_pred_type = Term.fastype_of rwd_pred
          val rwd_pred_type_error = TYPE ("type of RoboWorld predicate must be a (single-argument) function with the same input as the RoboWorld process and an output of boolean:",[rwd_type, rwd_pred_type],[rwd, rwd_pred])
          val _ = 
            case dest_Type rwd_pred_type of
                (@{type_name "fun"}, [inp, outp]) => if inp = inpT andalso outp = @{typ bool} then () else raise rwd_pred_type_error
              | _ => raise rwd_pred_type_error
          val consts_breadth = get_testgen_consts_breadth_opt ctxt
          val step_limit = get_testgen_step_limit_opt ctxt
          val timestep = get_testgen_timestep_opt ctxt
          val check_result_no_tick =  check_cyphycircus_has_trace_incremental_insts ctxt stT evT consts_breadth step_limit timestep trace false rwd rwd_pred
      in case check_result_no_tick of
            Exn.Res (SOME terms) => SOME terms
          | Exn.Res NONE => NONE
          | Exn.Exn e => (warning (exnMessage e); NONE)
      end\<close>

ML \<open>fun checkTraceOf ctxt (rwd : term) (rwd_pred : term) (trace : term list) = 
      Timeout.apply (Time.fromMilliseconds (get_testgen_timeout_opt ctxt)) (checkTraceOf' ctxt rwd rwd_pred trace) ()
      handle Timeout.TIMEOUT _ => (warning "checking timed out"; NONE)\<close>

section \<open>Testing algorithm\<close>

ML \<open>fun traceToProcess typ (trace : term list) =
          if null trace then
            Const (@{const_name Skip}, typ)
          else 
            let val evt_typ = fastype_of (hd trace)
            in Const (@{const_name SyncPrefix}, evt_typ --> typ --> typ) $ (hd trace) $ traceToProcess typ (tl trace)
            end\<close>

ML \<open>structure TraceSet = Set(type key = term list val ord = list_ord Term_Ord.fast_term_ord)\<close>
ML \<open>structure TermSet = Set(type key = term val ord = Term_Ord.fast_term_ord)\<close>

ML \<open>fun uncurry_term term =
      let val typ = fastype_of term
          val inpTs = Term.binder_types typ
          val free_names = Term.add_free_names term []
          val inps = map Free (Name.invent_names (Name.make_context free_names) "a" inpTs)
      in HOLogic.tupled_lambda (HOLogic.mk_tuple inps) (Term.list_comb (term, inps))
      end\<close>

ML \<open>fun term_string ctxt = Pretty.pure_string_of o Syntax.pretty_term ctxt
    fun traceToString ctxt trace = String.concatWith " \<rightarrow> " (map (term_string ctxt) trace)\<close>

ML \<open>fun testGeneration ctxt (rct: term) (muts: term list) (rwd: term) (rwd_pred: term) (n: int) = 
      let val rctType = fastype_of rct
          val rwd = uncurry_term rwd
          val rwd_pred = uncurry_term rwd_pred
          fun testGenLoop ctxt mutsToCheck refiningMuts failedMuts feasibleTrs infeasibleTrs i =
            (if get_testgen_verbose_opt ctxt then writeln ("Starting test generation iteration " ^ (Int.toString i)) else ();
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
                  (if get_testgen_verbose_opt ctxt then writeln ("Checking mutant " ^ (Syntax.string_of_term ctxt mut) ^ "...") else ();
                  case checkRefinement ctxt robochartPlusTraces mut of
                      (NONE, ctxt) => (
                        if get_testgen_verbose_opt ctxt then writeln ("refining mutant: " ^ (Syntax.string_of_term ctxt mut)) else ();
                        (TermSet.insert mut refMuts, failedMuts, traces, ctxt))
                    | (SOME NONE, ctxt) => (
                        if get_testgen_verbose_opt ctxt then  writeln ("failed mutant: " ^ (Syntax.string_of_term ctxt mut)) else ();
                        (refMuts, TermSet.insert mut failedMuts, traces, ctxt))
                    | (SOME (SOME trace), ctxt) => (
                        if get_testgen_verbose_opt ctxt then writeln ("trace generated: " ^ (traceToString ctxt trace)) else ();
                        (refMuts, failedMuts, TraceSet.insert trace traces, ctxt)))
                val (refMuts, failMuts, traces, ctxt) =
                      TermSet.fold checkMutant mutsToCheck (refiningMuts, failedMuts, TraceSet.empty, ctxt)
                fun checkTrace trace (fts, its, ctxt) =
                  (if get_testgen_verbose_opt ctxt then writeln ("Checking trace " ^ (traceToString ctxt trace) ^ "...") else ();
                  case checkTraceOf ctxt rwd rwd_pred trace of
                      NONE => (
                        if get_testgen_verbose_opt ctxt then  writeln ("feasible trace: " ^ traceToString ctxt trace) else ();
                        (TraceSet.insert trace fts, its, ctxt))
                    | SOME counterexamplePrefix => (
                        if get_testgen_verbose_opt ctxt then writeln ("infeasible trace counterexample: " ^ traceToString ctxt counterexamplePrefix) else ();
                        (fts, TraceSet.insert counterexamplePrefix its, ctxt)))
                val (fts, its, ctxt) = TraceSet.fold checkTrace traces (feasibleTrs, infeasibleTrs, ctxt)
                val newMutsToCheck = TermSet.subtract failMuts (TermSet.subtract refMuts mutsToCheck)
            in if i < n orelse TermSet.is_empty newMutsToCheck then testGenLoop ctxt newMutsToCheck refMuts failMuts fts its (i+1) else (refMuts, failMuts, fts, its, ctxt)
            end)
          val (refMuts, failMuts, fts, its, ctxt) =
            testGenLoop ctxt (TermSet.make muts) TermSet.empty TermSet.empty TraceSet.empty TraceSet.empty n
      in
        writeln "Feasible Traces Generated:";
        map (fn trace => (writeln ("  " ^ (traceToString ctxt trace)))) (TraceSet.dest fts);
        writeln "Refining mutants:";
        map (fn t => (writeln ("  " ^ (term_string ctxt t)))) (TermSet.dest refMuts);
        ctxt
      end\<close>

section \<open>Testing command\<close>

ML \<open>Outer_Syntax.local_theory \<^command_keyword>\<open>generate_tests_rct\<close>
  "generates tests from the semantics of a RoboChart model and its mutants, checking feasibility against a RoboWorld model"
  ((Parse.maybe Parse.options) -- (((Parse.$$$ "RoboChart" -- Parse.$$$ "=")  |-- Parse.term)
    -- ((Parse.$$$ "Mutants" -- Parse.$$$ "=")  |-- Parse.list1 Parse.term)
    -- ((Parse.$$$ "RoboWorld" -- Parse.$$$ "=")  |-- (Parse.term -- Parse.term))
    -- ((Parse.$$$ "Iterations" -- Parse.$$$ "=")  |-- Parse.nat))
  >> (fn (opts, (((rct, muts), (rwd, rwd_pred)), n)) => fn ctxt =>
      let val ctxt = parse_testgen_opts ctxt (Option.getOpt (opts, [])) 
          val rct_term = Syntax.read_term ctxt rct
          val mut_terms = map (Syntax.read_term ctxt) muts
          val rwd_term = Syntax.read_term ctxt rwd
          val rwd_pred_term = Syntax.read_term ctxt rwd_pred
      in testGeneration ctxt rct_term mut_terms rwd_term rwd_pred_term n
      end))\<close>

end