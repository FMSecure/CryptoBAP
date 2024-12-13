structure tree_to_processLib =
struct

local

    open HolKernel Parse
    open optionSyntax;
    open bir_envSyntax;
    open bir_programSyntax;
    open bir_valuesSyntax;
    open bir_immSyntax;
    open bir_expSyntax;
    open sbir_treeLib;
    open sapicplusTheory;
    open sapicplusSyntax;
    open translate_to_sapicTheory;
    open translate_to_sapicLib;
    open messagesTheory;
    open messagesSyntax;
    open bir_symbexec_treeLib; 
in


fun sapic_term_to_name trm =
    if (is_TVar trm)
    then (mk_Name (FreshName_tm, ((fst o dest_Var o dest_TVar) trm)))
    else if (is_Con trm)
    then (dest_Con trm)
    else  (mk_Name (PubName_tm, “"0"”))

fun read_events pred =
    let
	val event_names = bir_symbexec_oracleLib.read_fun_names "Event-Names";
	val pred_name = if (String.isSuffix "event_false_cnd" pred) then ("bad"^" "^(hd(event_names)))
			else if ((String.isSuffix "event_true_cnd" pred) orelse (String.isSuffix "event1" pred))
			then (List.nth (event_names, 1))
			else if (String.isSuffix "event2" pred)
			then (List.nth (event_names, 2))
			else if (String.isSuffix "event3" pred)
			then (List.nth (event_names, 3))
			else raise ERR "read_events" "cannot handle this pred";
	val namestr = stringSyntax.fromMLstring pred_name;
	val trm = mk_TVar (mk_Var (namestr,“0:int”));
    in
	trm
    end;
	    
	    
fun sbir_tree_sapic_process tree =
    case tree of
	VLeaf => ProcessNull_tm
      | VBranch ((a,b),lstr,rstr)  => mk_ProcessComb (NDC_tm,(sbir_tree_sapic_process lstr),(sbir_tree_sapic_process rstr))
      | VNode ((a,b),str)  =>  (
	let
	    val (name,bir_type) = dest_BVar a;
	    val namestr = stringSyntax.fromHOLstring name;
	in
	    if ((String.isSuffix "assert_true_cnd" namestr) orelse (String.isSuffix "T" namestr) orelse (String.isSuffix "init_pred" namestr) orelse (String.isSuffix "assert_false_cnd" namestr) orelse (String.isSuffix "cjmp_false_cnd" namestr) orelse (String.isSuffix "RepEnd" namestr))
	    then (sbir_tree_sapic_process str)
		 else if ((String.isSuffix "comp_true_cnd" namestr) orelse (String.isSuffix "cjmp_true_cnd" namestr))
	    then mk_ProcessComb ((mk_Cond (fst(bir_exp_to_sapic_term b))),(sbir_tree_sapic_process str),(ProcessNull_tm))
	    else if ((String.isSuffix "Key" namestr) orelse (String.isSuffix "iv" namestr) orelse (String.isSuffix "pkP" namestr) orelse (String.isSuffix "skS" namestr) orelse (String.isSuffix "RAND_NUM" namestr) orelse (String.isSuffix "OTP" namestr) orelse (String.isSuffix "SKey" namestr)  orelse (String.isSuffix "Epriv_i" namestr)  orelse (String.isSuffix "Epriv_r" namestr) orelse (String.isSuffix "sid_i" namestr)  orelse (String.isSuffix "sid_r" namestr) )
	    then  (mk_ProcessAction ((mk_New ((sapic_term_to_name o fst o bir_exp_to_sapic_term) b)),(mk_ProcessComb(mk_Let ((fst(bir_exp_to_sapic_term (mk_BExp_Den a))),((mk_Con o sapic_term_to_name o fst o bir_exp_to_sapic_term) b)),(sbir_tree_sapic_process str),(ProcessNull_tm)))))
	    else if ((String.isSuffix "K" namestr) orelse (String.isSuffix "Kr" namestr))
	    then (mk_ProcessAction ((mk_ChOut (mk_none(SapicTerm_t_ty),(fst(bir_exp_to_sapic_term b)))),(sbir_tree_sapic_process str)))
	    else if (String.isSuffix "Rep" namestr)
	    then (mk_ProcessAction (Rep_tm,(sbir_tree_sapic_process str)))
	    else if (String.isSuffix "Adv" namestr)
	    then (mk_ProcessAction ((mk_ChIn (mk_none(SapicTerm_t_ty),(fst(bir_exp_to_sapic_term b)))),(sbir_tree_sapic_process str)))
	    else if ((String.isSuffix "event_true_cnd" namestr) orelse (String.isSuffix "event1" namestr) orelse (String.isSuffix "event2" namestr) orelse (String.isSuffix "event3" namestr) orelse (String.isSuffix "event_false_cnd" namestr))
	    then (mk_ProcessAction ((mk_Event (mk_Fact(TermFact_tm,(listSyntax.mk_list ([(read_events namestr)],SapicTerm_t_ty))))),(sbir_tree_sapic_process str)))
	    else (mk_ProcessComb(mk_Let ((fst(bir_exp_to_sapic_term (mk_BExp_Den a))),(fst(bir_exp_to_sapic_term b))),(sbir_tree_sapic_process str),(ProcessNull_tm)))
	end)
			 
  
end(*local*)

end (* struct *)
