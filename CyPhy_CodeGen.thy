theory CyPhy_CodeGen
  imports CyPhy_Code
begin

section \<open>Code generation for supported CyPhyCircus terms\<close>

text \<open>
  The opaque \<open>cyphyaction\<close> carrier cannot be inspected by Isabelle's code
  generator.  The input process is already normalised by
  \<open>checkRefinement\<close>/\<open>rct_refine\<close>; this theory only translates it into
  executable \<open>cyphy_code\<close> syntax.
\<close>

ML \<open>
structure CyPhy_CodeGen =
struct

fun dest_action_type (T as Type (name, [eventT, _])) =
      if name = \<^type_name>\<open>cyphyaction\<close> then (T, eventT)
      else raise TYPE ("CyPhy_CodeGen: cyphyaction expected", [T], [])
  | dest_action_type T =
      raise TYPE ("CyPhy_CodeGen: cyphyaction expected", [T], [])

fun code_type eventT = Type (\<^type_name>\<open>cyphy_code\<close>, [eventT])

fun code_stop codeT = Const (\<^const_name>\<open>CodeStop\<close>, codeT)
fun code_skip codeT = Const (\<^const_name>\<open>CodeSkip\<close>, codeT)
fun code_prefix eventT codeT e P =
  Const (\<^const_name>\<open>CodePrefix\<close>, eventT --> codeT --> codeT) $ e $ P
fun code_ext codeT P Q =
  Const (\<^const_name>\<open>CodeExtChoice\<close>, codeT --> codeT --> codeT) $ P $ Q
fun code_int codeT P Q =
  Const (\<^const_name>\<open>CodeIntChoice\<close>, codeT --> codeT --> codeT) $ P $ Q
fun code_seq codeT P Q =
  Const (\<^const_name>\<open>CodeSeq\<close>, codeT --> codeT --> codeT) $ P $ Q
fun code_var codeT n =
  Const (\<^const_name>\<open>CodeVar\<close>, \<^typ>\<open>nat\<close> --> codeT) $
    HOLogic.mk_nat n
fun code_mu codeT P =
  Const (\<^const_name>\<open>CodeMu\<close>, codeT --> codeT) $ P

fun codegen_process eventT actionT process =
  let
    val codeT = code_type eventT
    fun codegen process =
      (case process of
        Const (name, _) =>
          if name = \<^const_name>\<open>cStop\<close> then code_stop codeT
          else if name = \<^const_name>\<open>cSkip\<close> then code_skip codeT
          else raise TERM ("unsupported normalised CyPhyCircus term", [process])
      | Const (name, _) $ e $ P =>
          if name = \<^const_name>\<open>cEventPrefix\<close>
          then code_prefix eventT codeT e (codegen P)
          else if name = \<^const_name>\<open>cExtChoice\<close>
          then code_ext codeT (codegen e) (codegen P)
          else if name = \<^const_name>\<open>cSeq\<close>
          then code_seq codeT (codegen e) (codegen P)
          else if name = \<^const_name>\<open>sup\<close>
               andalso Term.fastype_of process = actionT
          then code_int codeT (codegen e) (codegen P)
          else raise TERM ("unsupported normalised CyPhyCircus term", [process])
      | Const (name, _) $ Abs (_, boundT, body) =>
          if name = \<^const_name>\<open>gfp\<close> andalso boundT = actionT
          then code_mu codeT (codegen body)
          else raise TERM ("unsupported normalised CyPhyCircus term", [process])
      | Bound n => code_var codeT n
      | _ => raise TERM ("unsupported normalised CyPhyCircus term", [process]))
  in
    codegen process
  end

fun codegen_normalised ctxt normalised_process =
  let
    val (actionT, eventT) = dest_action_type (Term.fastype_of normalised_process)
  in
    codegen_process eventT actionT normalised_process |> Syntax.check_term ctxt
  end

end
\<close>

end
