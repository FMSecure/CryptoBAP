val _ =
  let
    fun first_env [] = NONE
      | first_env (name :: rest) =
          (case OS.Process.getEnv name of
             SOME path => SOME path
           | NONE => first_env rest);
    fun holba_dirs root =
      List.map
        (fn suffix => root ^ suffix)
        ["/src/extra",
         "/src/theory/bir",
         "/src/theory/bir-support",
         "/src/shared",
         "/src/shared/convs",
         "/src/shared/smt",
         "/src/tools/cfg",
         "/src/tools/exec",
         "/src/tools/lifter",
         "/src/tools/symbexec"];
  in
    case first_env ["HOLBADIR", "HOLBA_DIR"] of
      SOME root => loadPath := holba_dirs root @ (!loadPath)
    | NONE => ()
  end;

val _ =
  List.app load
    ["HolBACoreSimps",
     "HolBASimps",
     "bir_exp_substitutionsSyntax",
     "bir_programSyntax",
     "bir_valuesSyntax",
     "bir_immSyntax",
     "bir_expSyntax",
     "bir_exp_immSyntax",
     "bir_envSyntax",
     "bir_bool_expSyntax",
     "bir_program_labelsSyntax",
     "bir_typing_expSyntax",
     "bir_block_collectionLib",
     "bir_cfgLib",
     "bir_exec_typingLib",
     "bir_exp_typecheckLib",
     "bslSyntax",
     "bir_exp_to_wordsLib",
     "bir_smtLib",
     "Z3_SAT_modelLib"];

(* Compatibility state for the legacy symbolic executor.  The generated
   pipeline sets these values from the lifted program theory at startup. *)
structure binariesLib =
struct
  local
    open HolKernel Parse;
  in
    (* prog_lbl_tms_ is used by bir_symbexec_stateLib's tgt_bounds *)
    (* It will be set at pipeline initialization time *)
    val prog_lbl_tms_ : term list ref = ref []
    fun set_prog_lbl_tms tms = prog_lbl_tms_ := tms
    fun get_prog_lbl_tms () = !prog_lbl_tms_

    (* Compatibility values retained for legacy helper code. *)
    fun mem_find_symbol_addr_ (_:string) : Arbnum.num option = NONE
    val prog_vars : term list = []
    val binary_mem = fn (_:Arbnum.num) => (Arbnum.zero : Arbnum.num)
    val mem_sz_const = 0
    val mem_sz_globl = 0
    val mem_sz_stack = 0
    val pred_conjs : term list = []

    val bv_countw = ``T``  (* dummy *)
    val bv_mem = ``T``     (* dummy *)
    val bv_sp = ``T``      (* dummy *)
  end
end;
