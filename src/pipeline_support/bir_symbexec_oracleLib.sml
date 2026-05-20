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

structure bir_symbexec_oracleLib =
struct

local
    open binariesLib;
    open bir_symbexec_stateLib;
    open bir_symbexec_coreLib;
    open IntInf;
    open TextIO;
    open Redblackmap;
    open List;
    open bir_auxiliaryLib;
    open bir_cfgLib;
    open bir_expSyntax;
    open bir_programSyntax;
    open bir_immSyntax;
    open bir_envSyntax;
    open Hol_pp;
    open Term;
    open liteLib;
    open HolKernel Parse boolLib bossLib;
    open HolBACoreSimps;
    val ERR      = Feedback.mk_HOL_ERR "bir_symbexec_oracleLib"
in

(* detect function call based on label of block *)
fun is_function_call (n_dict : (term, cfg_node) Redblackmap.dict) (lbl_tm : term) =
    let
	val n_op = Redblackmap.peek(n_dict, lbl_tm);
	val exist = if is_none n_op
		    then false
		    else
			let
			    val n = valOf n_op;
			    val descr  = (valOf o #CFGN_hc_descr) n;
			    val instrDes = (snd o (list_split_pred #" ") o explode) descr;
			in
			    if ((String.isPrefix "(bl " (implode instrDes)) orelse (String.isPrefix "(b " (implode instrDes)) orelse (String.isPrefix "(blr " (implode instrDes)))
			    then true
			    else false
			  end;
    in
	exist
    end;

(* detect indirect jumps based on label of block *)

fun is_indirect_jmp (n_dict : (term, cfg_node) Redblackmap.dict) (lbl_tm : term) =
    let
	val n_op = Redblackmap.peek(n_dict, lbl_tm);
	val exist = if is_none n_op
		    then false
		    else
			let
			    val n = valOf n_op;
			    val descr  = (valOf o #CFGN_hc_descr) n;
			    val instrDes = (snd o (list_split_pred #" ") o explode) descr;
			in
			    if (String.isPrefix "(blr " (implode instrDes))
			    then true
			    else false
			  end;
    in
	exist
    end;  

(* fetch address of cjmp *)
fun state_exec_try_cjmp_label_out est syst =
     let
	 val cjmp_label_match_tm = ``BStmt_CJmp xyzc (BLE_Label xyz1) (BLE_Label xyz2)``;
	 val (vs, _) = hol88Lib.match cjmp_label_match_tm est;
	 val cnd     = fst (List.nth (vs, 0));
	 val tgt1    = fst (List.nth (vs, 1));
	 val tgt2    = fst (List.nth (vs, 2));

	 val cnd_exp_bool = if bir_expSyntax.is_BExp_Den cnd then
				bir_expSyntax.dest_BExp_Den cnd
			    else cnd;
				
     in
	 if bir_bool_expSyntax.is_bir_exp_true cnd_exp_bool then
             tgt1
	 else 
             tgt2

     end;


(* fetch address of jump from expression variable *)
fun state_exec_try_jmp_exp_var_out est syst =
    let
	val indjmps = SYST_get_indjmp syst;
	val tgt = (mk_BL_Address o bir_expSyntax.dest_BExp_Const o hd) indjmps;
    in
	tgt 
    end;

(* convert term into an integer *)    
fun sint_of_term tm =
  let
      fun from_label64 () =
          tm |> dest_BL_Address |> dest_Imm64 |> wordsSyntax.dest_word_literal |> Arbnum.toLargeInt;
      fun from_label32 () =
          tm |> dest_BL_Address |> dest_Imm32 |> wordsSyntax.dest_word_literal |> Arbnum.toLargeInt;
      fun from_word () =
          tm |> wordsSyntax.dest_word_literal |> Arbnum.toLargeInt;
  in
      from_label64 () handle HOL_ERR _ => (from_label32 () handle HOL_ERR _ => from_word ())
  end
  handle Overflow => raise ERR "sint_of_term"
                       ("integer " ^ term_to_string tm ^ " too large")
       | HOL_ERR _ => raise ERR "sint_of_term"
                       ("could not convert ``" ^ term_to_string tm ^
                        "`` to an integer");

fun in_range (mn:int,mx:int) tm =
    let val v = sint_of_term tm in
	mn <= v andalso v <= mx
    end handle HOL_ERR _ => false | Overflow => false;

fun equal_address address tm =
    let val v = sint_of_term tm in
     address <= v andalso v <= address
    end handle HOL_ERR _ => false | Overflow => false;

val stub_unclassified_calls = ref false;
val active_fragment_range = ref (NONE : (int * int) option);

fun set_stub_unclassified_calls enabled =
    stub_unclassified_calls := enabled;

fun get_stub_unclassified_calls () =
    !stub_unclassified_calls;

fun set_active_fragment_range (start_label : int, end_label : int) =
    active_fragment_range := SOME (start_label, end_label);

fun clear_active_fragment_range () =
    active_fragment_range := NONE;

fun label_in_active_fragment label =
    case !active_fragment_range of
        NONE => true
      | SOME (start_label, end_label) =>
          let val value = sint_of_term label in
            start_label <= value andalso value < end_label
          end
          handle HOL_ERR _ => true | Overflow => true;
     
(* Check whether a function name is in the adversary list (from pipeline.yaml) *)
fun is_adversary_function (fun_name : string) : bool =
    List.exists (fn x => x = fun_name)
                (pipelineConfigLib.get_adversary_functions ());

(* Check whether a function name is in the library list (from pipeline.yaml) *)
fun is_library_function (fun_name : string) : bool =
    List.exists (fn x => x = fun_name)
                (pipelineConfigLib.get_library_functions ());

     
fun fun_oracle_type_label adr_dict label =
    let
	open String;
	     
	val exist_dict = Redblackmap.peek(adr_dict, label);
        val callsite_crypto =
            case pipelineConfigLib.crypto_callsite_label_of (sint_of_term label) of
                SOME _ => true
              | NONE => false;
	    
	val lbl = 
	    (*critical section that no one must not jump to it*)
	    if callsite_crypto then
		"Library"
	    else if (case exist_dict of
		    SOME x => (is_adversary_function x)
		  | NONE => false)
	    then
		"Adversary"
	    (*part of memory that library functions exist*)
	    else if (case exist_dict of
			 SOME x => (is_library_function x)
		       | NONE => false)
	    then
		"Library"
            (*part of memory that loops exist*)
	    else if (case exist_dict of
		    SOME x => ((x >= "loop") andalso (x <= "loop"))
		  | NONE => false)
	    then
		"Loop"
	    else if (!stub_unclassified_calls) andalso not (label_in_active_fragment label)
	    then
		"Library"
	    (*jump to other part of memory is normal*)
	    else 
		"Normal";
	    
    in
	lbl
    end;

(* find address of function call *)     
fun fun_oracle_Address est syst =
    let
	val target_label = if is_BStmt_CJmp est then state_exec_try_cjmp_label_out est syst
			   else if is_BStmt_Halt est then (bir_expSyntax.dest_BExp_Const o dest_BStmt_Halt) est
			   else if (is_BLE_Label o dest_BStmt_Jmp) est then (dest_BLE_Label o dest_BStmt_Jmp) est
			   else if (is_BLE_Exp o dest_BStmt_Jmp) est then state_exec_try_jmp_exp_var_out est syst
			   else raise ERR "fun_orcle_Address" ("cannot handle target label " ^ (term_to_string est));
    in
	target_label
    end;

 (* detect type of function call *)   
fun fun_oracle adr_dict lbl_tm syst =
	(fun_oracle_type_label adr_dict lbl_tm);


(* detect type of cryptographic function call — now a simple map lookup
   via pipelineConfigLib instead of the old 34-slot positional list *)    
fun lib_oracle_type_label adr_dict label =
    case pipelineConfigLib.crypto_callsite_label_of (sint_of_term label) of
        SOME callsite_label => callsite_label
      | NONE =>
          (case Redblackmap.peek (adr_dict, label) of
              SOME find_from_dict => pipelineConfigLib.crypto_label_of find_from_dict
            | NONE => "C_Lib");

fun lib_oracle adr_dict lbl_tm syst =
    	(lib_oracle_type_label adr_dict lbl_tm);
  
    
end(*local*)

end (* struct *)




    
