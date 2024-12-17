
open HolKernel Parse boolLib bossLib;
open sumTheory;
open pred_setTheory;
open sigma_algebraTheory;
open listTheory;
open tautLib;
open interleavinggeneraldeductionTheory;
open parallelcompositiongeneraldeductionTheory;
open translate_to_sapicTheory;
open derived_rules_generaldeductionTheory;
open sbir_treeTheory;
open sapicplusTheory;
open messagesTheory;
open dolevyaoTheory;

val _ = new_theory "sbir_sapic_comp_DY";

(*
val comptraces_sapic_def =
Define`
      comptraces_sapic
      ((MTrn1:(SapicFact_t + (Name_t,Sig_t,Var_t) sync_event, 'SPpred, sapic_position_configuration_t, Var_t) mtrel),(Ded1:('SPpred) tded))
      ((MTrn2:(DYnsyc_event + (Name_t,Sig_t,Var_t) sync_event, DYpred, DYstate, Var_t) mtrel),(Ded2:(DYpred) tded))
      ((Sym:Var_t set),(P: ('SPpred + DYpred) set),(S1: sapic_position_configuration_t),(S2: DYstate))
      ((Sym':Var_t set),(P': ('SPpred + DYpred) set),(S1': sapic_position_configuration_t),(S2': DYstate))
=
{(t:((SapicFact_t + (Name_t,Sig_t,Var_t) sync_event)+(DYnsyc_event + (Name_t,Sig_t,Var_t) sync_event)) option list)|  
 (symbolicParlComp (MTrn1,Ded1) (MTrn2,Ded2) (Sym,P,S1,S2) t (Sym',P',S1',S2'))
}
`;

val comptraces_tree_def =
Define`
      comptraces_tree
      ((MTrn1:((sbir_event + (Name_t, Sig_t,Var_t) sync_event), 'SPpred, (sbir_event, real,(bir_var_t, bir_exp_t) symb_interpret_t) stree, Var_t) mtrel),(Ded1:('SPpred) tded))
      ((MTrn2:(DYnsyc_event + (Name_t,Sig_t,Var_t) sync_event, DYpred, DYstate, Var_t) mtrel),(Ded2:(DYpred) tded))
      ((Sym:Var_t set),(P: ('SPpred + DYpred) set),(S1: (sbir_event, real,(bir_var_t, bir_exp_t) symb_interpret_t) stree),(S2: DYstate))
      ((Sym':Var_t set),(P': ('SPpred + DYpred) set),(S1': (sbir_event, real,(bir_var_t, bir_exp_t) symb_interpret_t) stree),(S2': DYstate))
=
{(t: (((sbir_event + (Name_t,Sig_t, Var_t) sync_event) + DYnsyc_event + (Name_t,Sig_t,Var_t) sync_event) option list))|  
 (symbolicParlComp (MTrn1,Ded1) (MTrn2,Ded2) (Sym,P,S1,S2) t (Sym',P',S1',S2'))
}
`;

val sbirEvent_vs_Sync_to_sapicFact_vs_Sync_def =
Define`
      sbirEvent_vs_Sync_to_sapicFact_vs_Sync Ev =
( case Ev of
    NONE => NONE
  | SOME ((INL e):(sbir_event + (Name_t,Sig_t, Var_t) sync_event)) => SOME ((INL (sbirEvent_to_sapicFact e)):(SapicFact_t + (Name_t,Sig_t,Var_t) sync_event))
  | SOME ((INR e):(sbir_event + (Name_t,Sig_t, Var_t) sync_event)) => SOME ((INR e):(SapicFact_t + (Name_t,Sig_t,Var_t) sync_event))
)
`;

val sbirEvent_vs_DY_to_sapicFact_vs_DY_def =
Define`
      sbirEvent_vs_DY_to_sapicFact_vs_DY Ev =
( case Ev of
    NONE => NONE
  | SOME ((INL (INL e)):((sbir_event + (Name_t, Sig_t,Var_t) sync_event) + DYnsyc_event + (Name_t,Sig_t,Var_t) sync_event)) => SOME ((INL (INL (sbirEvent_to_sapicFact e))):((SapicFact_t + (Name_t,Sig_t,Var_t) sync_event)+(DYnsyc_event + (Name_t,Sig_t,Var_t) sync_event)))
  | SOME ((INL (INR e)):((sbir_event + (Name_t, Sig_t,Var_t) sync_event) + DYnsyc_event + (Name_t,Sig_t,Var_t) sync_event)) => SOME ((INL (INR e)):((SapicFact_t + (Name_t,Sig_t,Var_t) sync_event)+(DYnsyc_event + (Name_t,Sig_t,Var_t) sync_event)))
  | SOME ((INR (INL e)):((sbir_event + (Name_t, Sig_t,Var_t) sync_event) + DYnsyc_event + (Name_t,Sig_t,Var_t) sync_event)) => SOME ((INR (INL e)):((SapicFact_t + (Name_t,Sig_t,Var_t) sync_event)+(DYnsyc_event + (Name_t,Sig_t,Var_t) sync_event)))
  | SOME ((INR (INR e)):((sbir_event + (Name_t, Sig_t,Var_t) sync_event) + DYnsyc_event + (Name_t,Sig_t,Var_t) sync_event)) => SOME ((INR (INR e)):((SapicFact_t + (Name_t,Sig_t,Var_t) sync_event)+(DYnsyc_event + (Name_t,Sig_t,Var_t) sync_event)))
)
`;


val binterl_sbir_to_sapic_thm = store_thm(
  "binterl_sbir_to_sapic_thm",
  ``∀t t1 t2.
       binterl t1 t2 t
     ==>
     binterl (MAP sbirEvent_vs_Sync_to_sapicFact_vs_Sync t1) t2
             (MAP sbirEvent_vs_DY_to_sapicFact_vs_DY t) ``,
             gen_tac >>
     Induct_on ‘t’ >-(
      rpt strip_tac >>     
      FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [MAP] >>
      IMP_RES_TAC binterl_Empty >>
      rw[binterl_nil]
      )(*Nil*) >>
     rpt strip_tac >>
     IMP_RES_TAC binterl_NotEmpty >>
     rw[] >>
     PAT_X_ASSUM ``!t1 t2. A`` (ASSUME_TAC o (Q.SPECL [‘(t1':(sbir_event + (Name_t,Sig_t, Var_t) sync_event) option list)’,‘(t2':(DYnsyc_event + (Name_t, Sig_t,Var_t) sync_event) option list)’])) >>
     IMP_RES_TAC binterl_Conj >>
     RES_TAC >>
     Cases_on ‘h’ >-(
      IMP_RES_TAC binterl_moveNONE >>
      rw[] >>
      FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [sbirEvent_vs_DY_to_sapicFact_vs_DY_def,sbirEvent_vs_Sync_to_sapicFact_vs_Sync_def] >>  
      metis_tac[binterl_none]
      )(*NONE*) >>
     Cases_on ‘x’ >- (
      Cases_on ‘x'’ >- (
        IMP_RES_TAC binterl_moveNAL >>
        rw[] >>
        FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [sbirEvent_vs_DY_to_sapicFact_vs_DY_def,sbirEvent_vs_Sync_to_sapicFact_vs_Sync_def] >>
        metis_tac [binterl_leftN]       
        )(*(INL (INL x))*) >>
      IMP_RES_TAC binterl_moveSL >>
      rw[] >>
      FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [sbirEvent_vs_DY_to_sapicFact_vs_DY_def,sbirEvent_vs_Sync_to_sapicFact_vs_Sync_def] >>
      metis_tac [binterl_syncL]
      )(*INL x'*) >> 
     Cases_on ‘y’ >- (
      IMP_RES_TAC binterl_moveNAR >>
      rw[] >>
      FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [sbirEvent_vs_DY_to_sapicFact_vs_DY_def,sbirEvent_vs_Sync_to_sapicFact_vs_Sync_def] >>
      metis_tac [binterl_rightN]      
      )(*(INR (INL x))*) >>
     IMP_RES_TAC binterl_moveSR >>
     rw[] >>
     FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [sbirEvent_vs_DY_to_sapicFact_vs_DY_def,sbirEvent_vs_Sync_to_sapicFact_vs_Sync_def] >>
     metis_tac [binterl_syncR]
  );

val compose_sbir_sapic_vs_DY_thm = store_thm(
  "compose_sbir_sapic_vs_DY_thm",
  ``∀T0 Re0 NRe0 i Re NRe Tre (Sym:(Var_t -> bool)) (Sym':(Var_t -> bool)) (P:('SPpred + DYpred -> bool)) (P':('SPpred + DYpred -> bool)) (Ded:('SPpred) tded) (ded3:('SPpred + DYpred) tded).
        ((IMAGE (MAP sbirEvent_vs_Sync_to_sapicFact_vs_Sync) (traces_of_tree_with_symb (Sym,IMAGE OUTL P,T0) (Sym',IMAGE OUTL P',Tre))) ⊆ (traces_of_sapic_with_symb (Sym,IMAGE OUTL P,(Pconfig ((symbtree_to_sapic T0),0,Re0,NRe0))) (Sym',IMAGE OUTL P',(Pconfig ((symbtree_to_sapic Tre),i,Re,NRe)))))
     ==> (
      (IMAGE (MAP sbirEvent_vs_DY_to_sapicFact_vs_DY) (comptraces_tree (symbolic_tree_multi_transitions_with_symb,Ded) (DYmultranrel,DYdeduction) (Sym,P,T0,ESt) (Sym',P',Tre,ESt))) ⊆
      (comptraces_sapic (sapic_position_multi_transitions_with_symb,Ded) (DYmultranrel,DYdeduction) (Sym,P,(Pconfig ((symbtree_to_sapic T0),0,Re0,NRe0)),ESt) (Sym',P',(Pconfig ((symbtree_to_sapic Tre),i,Re,NRe)),ESt))
      ) ``,
        FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [traces_of_tree_with_symb_def,traces_of_sapic_with_symb_def,EXTENSION,SUBSET_DEF,comptraces_tree_def, comptraces_sapic_def,binterleave_composition_deduction,binterleave_ts,binterleave_trace_deduction] >>    
     rpt strip_tac >>
     PAT_X_ASSUM ``!x. A`` (ASSUME_TAC o (Q.SPECL [`(MAP sbirEvent_vs_Sync_to_sapicFact_vs_Sync t1)`])) >>
     RES_TAC  >>
     FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [sbirEvent_vs_Sync_to_sapicFact_vs_Sync_def,MAP] >>
     Q.EXISTS_TAC `(MAP sbirEvent_vs_Sync_to_sapicFact_vs_Sync t1)` >>
     Q.EXISTS_TAC `t2` >>
     FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [binterl_sbir_to_sapic_thm]
  );


*)
val _ = export_theory();

