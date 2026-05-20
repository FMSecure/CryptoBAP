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

structure bir_symbexec_PreprocessLib =
struct

local
    open HolKernel Parse;
    open binariesLib;
    open bir_programSyntax;
    open bir_valuesSyntax;
    open bir_immSyntax;
    open bir_exec_typingLib;
    open bir_cfgLib;
    open bir_block_collectionLib;
    open bir_envSyntax;
    open bir_expSyntax;
    open bir_auxiliaryLib;
    open bir_immSyntax;
    open wordsSyntax;
    open String;
    open bir_program_labelsSyntax;
    open bir_block_collectionLib;
    open Redblackmap;
    open Term;
  val ERR      = Feedback.mk_HOL_ERR "bir_symbexec_PreprocessLib"
in
    
(* Find nodes with branch*)
fun fun_address_dict (n:cfg_node) =
    let
        val lbl_tm   = #CFGN_lbl_tm n;
	val descr  = (valOf o #CFGN_hc_descr) n;
	val instrDes = (snd o (list_split_pred #" ") o explode) descr;
	   (* val _ = print ((implode instrDes) ^ "\n"); *)
	val name_adr = if (isPrefix "(bl " (implode instrDes))
		       then let
			       val fname = (implode o fst o (list_split_pred #">") o snd o (list_split_pred #"<")) instrDes;
			   in
			       (lbl_tm, fname)
			   end
		       else if (isPrefix "(blr " (implode instrDes))
		       then let
			       val fname = (implode o fst o (list_split_pred #")") o snd o (list_split_pred #" ")) instrDes;
			   in
			       (lbl_tm, fname)
			   end
		       else if (isPrefix "(b " (implode instrDes))
		       then let
			       val fname = if (isPrefix "(b <" (implode instrDes))
					   then
					       (implode o fst o (list_split_pred #">") o snd o (list_split_pred #"<")) instrDes
					   else
					       (implode o fst o (list_split_pred #")") o snd o (list_split_pred #" ")) instrDes
			   in
			       (lbl_tm, fname)
			   end
		       else (“BL_Address (Imm32 0w)”, " ");
    in
	name_adr
    end;
    
(* Find address of nodes with branch*)     
fun fun_addresses_dict bl_dict prog_lbl_tms =
    let
	val n_dict = bir_cfgLib.cfg_build_node_dict bl_dict prog_lbl_tms;
	    
	val func_table = Redblackmap.mkDict Term.compare : (term, string) Redblackmap.dict;

	val fun_adr = (List.map (fn x => (fun_address_dict x)) (List.map snd (Redblackmap.listItems n_dict)));

	val func_table' = Redblackmap.insertList (func_table, fun_adr);
    in
	fst (Redblackmap.remove(func_table', “BL_Address (Imm32 0w)”))
    end;
  
end(*local*)

end (* struct *)
