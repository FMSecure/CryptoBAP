open HolKernel Parse boolLib bossLib;
open sumTheory;
open optionTheory;
open pred_setTheory;
open sigma_algebraTheory;
open listTheory;
open tautLib;
open interleavinggeneraldeductionTheory;
open parallelcompositiongeneraldeductionTheory;

val _ = new_theory "derived_rules_generaldeduction";

val traces_def =
Define`
      traces ((MTrn:('event, 'pred, 'state, 'symb) mtrel),(ded:('pred) tded)) ((Sym:'symb set),(P: 'pred set),(S: 'state)) ((Sym':'symb set),(P': 'pred set),(S': 'state)) = {t| (MTrn (Sym,P,S) t (Sym',P',S'))}
                                                                                                                                                                             `;
val comptraces_def =
Define`
      comptraces ((MTrn1:('event1 + 'eventS, 'pred1, 'state1, 'symb) mtrel),(Ded1:('pred1) tded)) ((MTrn2:('event2 + 'eventS, 'pred2, 'state2, 'symb) mtrel),(Ded2:('pred2) tded)) (ded3:('pred1 + 'pred2) tded) ((Sym:'symb set),(P: ('pred1 + 'pred2) set),(S1: 'state1),(S2: 'state2)) ((Sym':'symb set),(P': ('pred1 + 'pred2) set),(S1': 'state1),(S2': 'state2)) =
{(t: ((('event1 + 'eventS) + 'event2 + 'eventS) option list))|  
 (symbolicParlComp (MTrn1,Ded1) (MTrn2,Ded2) ded3 (Sym,P,S1,S2) t (Sym',P',S1',S2'))
}
`;


val RevDed_def =
Define `
       (RevDed (ded:('pred1 + 'pred2) tded) phi p  =  (∀(n: 'pred2 -> 'pred1) (m: 'pred1 -> 'pred2). ded (IMAGE (SUM_MAP n m) phi) ((SUM_MAP n m) p))
       )`;


val IMAGE_SUM_MAP_RI_thm = store_thm(
  "IMAGE_SUM_MAP_RI",
  ``
∀ P n.
IMAGE OUTR (IMAGE (SUM_MAP n I) P) = IMAGE OUTR P
``,
      rpt strip_tac >>
      Cases_on ‘P’ >-(
 FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)[]
  ) >>
 FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)[IMAGE_INSERT,SUM_MAP_CASE] >>
  Cases_on ‘x’ >- (
 FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)[sum_case_def] >>
metis_tac[OUTR_INL_FUN]
) >>
 FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)[sum_case_def] >> 
  metis_tac[OUTL_INR_FUN]
)

val IMAGE_SUM_MAP_LI_thm = store_thm(
  "IMAGE_SUM_MAP_LI",
  ``
∀ P n.
IMAGE OUTL (IMAGE (SUM_MAP I n) P) = IMAGE OUTL P
``,
      rpt strip_tac >>
      Cases_on ‘P’ >-(
 FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)[]
  ) >>
 FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)[IMAGE_INSERT,SUM_MAP_CASE] >>
  Cases_on ‘x’ >- (
 FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)[sum_case_def] >>
metis_tac[OUTR_INL_FUN]
) >>
 FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)[sum_case_def] >> 
  metis_tac[OUTL_INR_FUN]
  )

val IMAGE_SUM_MAP_R2L_thm = store_thm(
  "IMAGE_SUM_MAP_R2L",
  ``
∀ P n m.
IMAGE OUTR P = IMAGE OUTL (IMAGE (SUM_MAP n m) P)
``,
      rpt strip_tac >>
      Cases_on ‘P’ >-(
 FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)[]
  ) >>
 FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)[IMAGE_INSERT,SUM_MAP_CASE] >>
  Cases_on ‘x’ >- (
 FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)[sum_case_def] >>
metis_tac[OUTR_INL_FUN]
) >>
 FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)[sum_case_def] >> 
  metis_tac[OUTL_INR_FUN]
)

val IMAGE_SUM_MAP_L2R_thm = store_thm(
  "IMAGE_SUM_MAP_L2R",
  ``
∀ P n m.
IMAGE OUTL P = IMAGE OUTR (IMAGE (SUM_MAP n m) P)
``,
      rpt strip_tac >>
      Cases_on ‘P’ >-(
 FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)[]
  ) >>
 FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)[IMAGE_INSERT,SUM_MAP_CASE] >>
  Cases_on ‘x’ >- (
 FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)[sum_case_def] >>
metis_tac[OUTR_INL_FUN]
) >>
 FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)[sum_case_def] >> 
  metis_tac[OUTL_INR_FUN]
)

        
val symmetry_generaldeduction_thm = store_thm(
  " symmetry_generaldeduction",
  ``∀t f g  n m Sym P P' S1 S2 Sym' S1' S2'  (MTrn1:('event1 + 'eventS, 'pred1, 'state1, 'symb) mtrel) (MTrn2:('event2 + 'eventS, 'pred2, 'state2, 'symb) mtrel) (ded1:('pred1) tded) (ded2:('pred2) tded) (ded3:('pred1 + 'pred2) tded) (ded4:('pred2 + 'pred1) tded).
       (symbolicParlComp (MTrn1,ded1) (MTrn2,ded2) ded3 (Sym,P,S1,S2) t (Sym',P',S1',S2'))
     =
     (symbolicParlComp (MTrn2,ded2) (MTrn1,ded1) (RevDed ded3) (Sym,(IMAGE (SUM_MAP n m) P),S2,S1) (MAP (OPTION_MAP (SUM_MAP f g)) t) (Sym',(IMAGE (SUM_MAP n m) P'),S2',S1')) 
 ``,
 GEN_TAC >>
     Induct_on `t` >- (
      FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)[] >>
      rpt strip_tac >>
      EQ_TAC >-(
        FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)[symbolicParlComp_def] >>
        rw[] >-(
          metis_tac[IMAGE_SUM_MAP_R2L_thm]
          ) >>
        metis_tac[IMAGE_SUM_MAP_L2R_thm]
        ) >>
        FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)[symbolicParlComp_def] >>
        rw[] >-(
          Cases_on ‘P’ >-(
            FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)[]
            ) >>
          FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)[IMAGE_INSERT,SUM_MAP_CASE] >>
          Cases_on ‘x’ >- (
            FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)[sum_case_def] >>
            metis_tac[OUTR_INL_FUN]
            ) >>
          FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)[sum_case_def] >> 
          metis_tac[OUTL_INR_FUN]
          ) >- (
          metis_tac[IMAGE_SUM_MAP_L2R_thm]
          ) >>
        metis_tac[IMAGE_SUM_MAP_R2L_thm]
                ) >>
        gen_tac >>
     Cases_on `h` >-(
 FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)[symbolicParlComp_def] >>
          rpt strip_tac >>
          EQ_TAC >- (
rpt strip_tac >>
Q.EXISTS_TAC `IMAGE (SUM_MAP n m) P''` >>
rw[] >- (
 PAT_X_ASSUM ``!phi. A`` (ASSUME_TAC o (Q.SPECL [`((SUM_MAP (m: 'pred2 -> 'pred1) (n: 'pred1 -> 'pred2)) phi)`])) >>
 IMP_RES_TAC combineAllDed_def >-(



            )
          )



)

              )





















      (
          FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)[symbolicParlComp_def] >>
          rpt strip_tac >>
          EQ_TAC >- (
            rpt strip_tac >>
            FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)[RevDed_def] >>
            Q.EXISTS_TAC `IMAGE (SUM_MAP n m) P''` >>
            rw[] >- (
                  PAT_X_ASSUM ``!phi. A`` (ASSUME_TAC o (Q.SPECL [`((SUM_MAP (m: 'pred2 -> 'pred1) (n: 'pred1 -> 'pred2)) phi)`])) >>

                  FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)[combineAllDed_def] >- (

            Cases_on ‘phi’ >- (

FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)[composeDed_def] >>
metis_tac[IMAGE_SUM_MAP_R2L_thm]

                     )
            )
                                                                                                                                                
              )

            )

          )




                      
∀ P n m.
IMAGE OUTR P = IMAGE OUTL (IMAGE (SUM_MAP n m) P)

      rpt strip_tac >>
      Cases_on ‘P’ >-(
 FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)[]
  ) >>
 FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)[IMAGE_INSERT,SUM_MAP_CASE] >>
  Cases_on ‘x’ >- (
 FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)[sum_case_def] >>
metis_tac[OUTR_INL_FUN]
) >>
 FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)[sum_case_def] >> 
  metis_tac[OUTL_INR_FUN]

 
   FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)[IMAGE_INSERT,SUM_MAP_CASE]
    FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)[]
    FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)[sum_case_def]
metis_tac[OUTR_INL_FUN]

        
∀x n.
 OUTR (INL x) = n x
      
∀x n.
 OUTL (INR x) = n x
 
rpt strip_tac >>
      PAT_X_ASSUM ``!phi. A`` (ASSUME_TAC o (Q.SPECL [`phi`])) >>
      PAT_X_ASSUM ``!Sym P S1 S2 Sym' P' S1' S2' MTrn1 MTrn2 ded1 ded2 ded3. A`` (ASSUME_TAC o (Q.SPECL [`Sym`,`P`,`S1`,`S2`,`Sym'`,`P''`,`S1'`,`S2'`,`MTrn1`,`MTrn2`,`ded1`,`ded2`,`ded3`]))>>
      RES_TAC >>
      Q.EXISTS_TAC `t1` >>
      Q.EXISTS_TAC `t2` >>
      FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)[]>>
      metis_tac[] 
                        

                
            PAT_X_ASSUM ``!x. A`` (ASSUME_TAC o (Q.SPECL [`(INR b)`])) >>
                 rw[] >>
                 RES_TAC

              )
                       
               )     
        FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)[symbolicParlComp_def,disjUNION_def,IMAGE_DEF] >>

,UNION_DEF,EXTENSION
,sum_CASES,FORALL_SUM
FORALL_SUM
 FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)[disjUNION_def]

 FULL_SIMP_TAC (list_ss) [SUM_UNIV]

SUM_UNIV
GSPEC_OR
        )
                        
    )            
                   
      rpt strip_tac >>
      EQ_TAC >-(
             FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)[symbolicParlComp_def,disjUNION_def]

               )
      Q.EXISTS_TAC `[]` >>
      Q.EXISTS_TAC `[]` >>
      metis_tac[binterl_nil]) >>
     gen_tac >>
     Cases_on `h` >- (



        )
      )
  )




val two_sapics_DY_comptraces_thm =
INST_TYPE [``:'pred1`` |-> ``:'pred2``,``:'pred2`` |-> ``:'pred1``] (ded:('pred1 + 'pred2) tded);
val two_sapics_DY_comptraces_t = (fst o strip_comb o fst o dest_eq o snd o strip_forall o concl) two_sapics_DY_comptraces_thm;
val two_sapics_DY_comptraces_def = Define `
    two_sapics_DY_comptraces = ^(two_sapics_DY_comptraces_t)
`;


        val RevDed_def =
Define `
       (RevDed (ded:('pred1 + 'pred2) tded) phi p  =  (∀(n: 'pred2 -> 'pred1) (m: 'pred1 -> 'pred2). ded (IMAGE (SUM_MAP n m) phi) ((SUM_MAP n m) p))
)`;
  
 ∀(ded:('pred1 + 'pred2) tded) phi (n: 'pred1 -> 'pred2) (m: 'pred2 -> 'pred1) p. ded phi p ⇒ (SUM_REV ded) (IMAGE (SUM_MAP n m) phi) ((SUM_MAP n m) p)
       
OPTION_MAP_CASE

∀t f g  n m Sym P P' S1 S2 Sym' P' S1' S2'  (MTrn1:('event1 + 'eventS, 'pred1, 'state1, 'symb) mtrel) (MTrn2:('event2 + 'eventS, 'pred2, 'state2, 'symb) mtrel) (ded1:('pred1) tded) (ded2:('pred2) tded) (ded3:('pred1 + 'pred2) tded) (ded4:('pred2 + 'pred1) tded).
       (symbolicParlComp (MTrn1,ded1) (MTrn2,ded2) ded3 (Sym,P,S1,S2) t (Sym',P',S1',S2'))
     =
     (symbolicParlComp (MTrn2,ded2) (MTrn1,ded1) ded4 (Sym,(IMAGE (SUM_MAP n m) P),S2,S1) (MAP (OPTION_MAP (SUM_MAP f g)) t) (Sym',(IMAGE (SUM_MAP n m) P'),S2',S1')) 


option_case_def
  
val symmetry_generaldeduction_thm = store_thm(
  " symmetry_generaldeduction",
  ``∀(t1:('event1 + 'eventS) option list) (t2:('event2 + 'eventS) option list) Sym P1 P2 P1' P2' S1 S2 Sym' P' S1' S2'  (MTrn1:('event1 + 'eventS, 'pred1, 'state1, 'symb) mtrel) (MTrn2:('event2 + 'eventS, 'pred2, 'state2, 'symb) mtrel) (ded1:('pred1) tded) (ded2:('pred2) tded) (ded3:('pred1 + 'pred2) tded) (ded4:('pred2 + 'pred1) tded).
       (symbolicParlComp (MTrn1,ded1) (MTrn2,ded2) ded3 (Sym,(P1 ⊔ P2),S1,S2) (MAP SOME (APPEND (MAP (INL o THE) t1) (MAP (INR o THE) t2))) (Sym',(P1' ⊔ P2'),S1',S2'))
     =
     (symbolicParlComp (MTrn2,ded2) (MTrn1,ded1) ded4 (Sym,(P2 ⊔ P1),S2,S1) (MAP SOME (APPEND (MAP (INL o THE) t2) (MAP (INR o THE) t1))) (Sym',(P2' ⊔ P1'),S2',S1')) ``,
     GEN_TAC >>
     Induct_on `t1` >- (
      FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)[] >>
      GEN_TAC >>
      Induct_on `t2` >- (
           rpt strip_tac >>
      EQ_TAC >-(
          FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)[symbolicParlComp_def] >>
          rw[] >-(
          FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)[disjUNION_def,UNION_DEF,EXTENSION] >>
          GEN_TAC >>
          EQ_TAC >-(
                 rw[] >- (
                 PAT_X_ASSUM ``!x. A`` (ASSUME_TAC o (Q.SPECL [`(INR a)`])) >>
                 rw[] >>
                 RES_TAC
                 ) >>
                 PAT_X_ASSUM ``!x. A`` (ASSUME_TAC o (Q.SPECL [`(INL b)`])) >>
                 rw[] >>
                 RES_TAC               
              ) >>
          rw[] >- (
                 PAT_X_ASSUM ``!x. A`` (ASSUME_TAC o (Q.SPECL [`(INR a)`])) >>
                 rw[] >>
                 RES_TAC
                 ) >>
                 PAT_X_ASSUM ``!x. A`` (ASSUME_TAC o (Q.SPECL [`(INL b)`])) >>
                 rw[] >>
                 RES_TAC    
            ) (*Proved P2 ⊔ P1 = P2' ⊔ P1' *) >- (
            FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)[OUTL_disjUNION,OUTR_disjUNION] 
            ) >>
            FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)[OUTL_disjUNION,OUTR_disjUNION] 

            
  val symmetry_generaldeduction_thm = store_thm(
  " symmetry_generaldeduction",
  ``∀(t1:('event1 + 'eventS) option list) (t2:('event2 + 'eventS) option list) Sym P1 P2 P1' P2' S1 S2 Sym' P' S1' S2'  (MTrn1:('event1 + 'eventS, 'pred1, 'state1, 'symb) mtrel) (MTrn2:('event2 + 'eventS, 'pred2, 'state2, 'symb) mtrel) (ded1:('pred1) tded) (ded2:('pred2) tded) (ded3:('pred1 + 'pred2) tded) (ded4:('pred2 + 'pred1) tded).
       (symbolicParlComp (MTrn1,ded1) (MTrn2,ded2) ded3 (Sym,(P1 ⊔ P2),S1,S2) (MAP SOME (APPEND (MAP (INL o THE) t1) (MAP (INR o THE) t2))) (Sym',(P1' ⊔ P2'),S1',S2'))
     =
     (symbolicParlComp (MTrn2,ded2) (MTrn1,ded1) ded4 (Sym,(P2 ⊔ P1),S2,S1) (MAP SOME (APPEND (MAP (INL o THE) t2) (MAP (INR o THE) t1))) (Sym',(P2' ⊔ P1'),S2',S1'))
     ``,
*)
val binterleave_trace_comp_to_decomp_generaldeduction_thm = store_thm(
  "binterleave_trace_comp_to_decomp_generaldeduction",
  ``∀t Sym P S1 S2 Sym' P' S1' S2' (MTrn1:('event1 + 'eventS, 'pred1, 'state1, 'symb) mtrel) (MTrn2:('event2 + 'eventS, 'pred2, 'state2, 'symb) mtrel) (ded1:('pred1) tded) (ded2:('pred2) tded) (ded3:('pred1 + 'pred2) tded).
       (TransDisable ded3 (MTrn1,ded1) (MTrn2,ded2)) ⇒
       ((symbolicParlComp (MTrn1,ded1) (MTrn2,ded2) ded3 (Sym,P,S1,S2) t (Sym',P',S1',S2'))
     ⇒
     (∃t1 t2.
        (MTrn1 (Sym,(IMAGE OUTL P),S1) t1 (Sym',(IMAGE OUTL P'),S1')) ∧
        (MTrn2 (Sym,(IMAGE OUTR P),S2) t2 (Sym',(IMAGE OUTR P'),S2')) ∧
        (binterl t1 t2 t)))``,
                          GEN_TAC >>
     Induct_on `t` >- (
      FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)[symbolicParlComp_def]>>     
      rpt strip_tac >>
      Q.EXISTS_TAC `[]` >>
      Q.EXISTS_TAC `[]` >>
      metis_tac[binterl_nil]) >>
     gen_tac >>
     Cases_on `h` >- (
      FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)[symbolicParlComp_def] >>
      rpt strip_tac >>
      PAT_X_ASSUM ``!phi. A`` (ASSUME_TAC o (Q.SPECL [`phi`])) >>
      PAT_X_ASSUM ``!Sym P S1 S2 Sym' P' S1' S2' MTrn1 MTrn2 ded1 ded2 ded3. A`` (ASSUME_TAC o (Q.SPECL [`Sym`,`P`,`S1`,`S2`,`Sym'`,`P''`,`S1'`,`S2'`,`MTrn1`,`MTrn2`,`ded1`,`ded2`,`ded3`]))>>
      RES_TAC >>
      Q.EXISTS_TAC `t1` >>
      Q.EXISTS_TAC `t2` >>
      FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)[]>>
      metis_tac[TransDisable_def,binterl_combinenone] 
      )   >>
     Cases_on `x` >-(
      Cases_on `x'` >-(
        FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [symbolicParlComp_def] >>
        rpt strip_tac >>
        PAT_X_ASSUM ``!Sym P S1 S2 Sym' P' S1' S2' MTrn1 MTrn2 ded1 ded2 ded3. A`` (ASSUME_TAC o (Q.SPECL [`Sym`,`P`,`S1`,`S2`,`Sym'''`,`P'''`,`S1'''`,`S2'`,`MTrn1`,`MTrn2`,`ded1`,`ded2`,`ded3`])) >>
        RES_TAC >>
        Q.EXISTS_TAC `(SOME (INL x))::t1` >>
        Q.EXISTS_TAC `t2` >>
        metis_tac[TranRelNil,TranRelSnoc,TranRelConfigEq,binterl_left]
        ) >>
      FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [symbolicParlComp_def] >>
      rpt strip_tac >>
      PAT_X_ASSUM ``!Sym P S1 S2 Sym' P' S1' S2' MTrn1 MTrn2. A`` (ASSUME_TAC o (Q.SPECL [`Sym`,`P`,`S1`,`S2`,`Sym'''`,`P'''`,`S1'''`,`S2'''`,`MTrn1`,`MTrn2`])) >>
      RES_TAC >>
      Q.EXISTS_TAC `(SOME (INR y))::t1` >>
      Q.EXISTS_TAC `(SOME (INR y))::t2` >>
      rw[binterl_syncL] >- (metis_tac[TranRelSnoc])  >>
      metis_tac[TranRelSnoc]
      ) >>
     Cases_on `y` >- (
      FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [symbolicParlComp_def] >>
      rpt strip_tac >>
      PAT_X_ASSUM ``!Sym P S1 S2 Sym' P' S1' S2' MTrn1 MTrn2. A`` (ASSUME_TAC o (Q.SPECL [`Sym`,`P`,`S1`,`S2`,`Sym'''`,`P'''`,`S1'`,`S2'''`,`MTrn1`,`MTrn2`])) >>
      RES_TAC >>
      Q.EXISTS_TAC `t1` >>
      Q.EXISTS_TAC `(SOME (INL x))::t2` >>
      metis_tac[binterl_right,TranRelNil,TranRelSnoc,TranRelConfigEq])>>
     FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [symbolicParlComp_def] >>
     rpt strip_tac >>
     PAT_X_ASSUM ``!Sym P S1 S2 Sym' P' S1' S2' MTrn1 MTrn2. A`` (ASSUME_TAC o (Q.SPECL [`Sym`,`P`,`S1`,`S2`,`Sym'''`,`P'''`,`S1'''`,`S2'''`,`MTrn1`,`MTrn2`])) >>
     RES_TAC >>
     Q.EXISTS_TAC `(SOME (INR y'))::t1` >>
     Q.EXISTS_TAC `(SOME (INR y'))::t2` >>
     metis_tac[binterl_syncR,TranRelSnoc]
  );


val binterleave_composition_generaldeduction_subseteq_thm = store_thm(
  "binterleave_composition_generaldeduction_subseteq",
  ``∀Sym P S1 S2 Sym' P' S1' S2' (MTrn1:('event1 + 'eventS, 'pred1, 'state1, 'symb) mtrel) (MTrn2:('event2 + 'eventS, 'pred2, 'state2, 'symb) mtrel) (Ded1:('pred1) tded) (Ded2:('pred2) tded) (ded3:('pred1 + 'pred2) tded).
         (TransDisable ded3 (MTrn1,Ded1) (MTrn2,Ded2)) ⇒
         ((comptraces (MTrn1,Ded1) (MTrn2,Ded2) ded3 (Sym,P,S1,S2) (Sym',P',S1',S2'))                           
      ⊆ (binterleave_ts (traces (MTrn1,Ded1) (Sym,(IMAGE OUTL P),S1) (Sym',(IMAGE OUTL P'),S1')) (traces (MTrn2,Ded2) (Sym,(IMAGE OUTR P),S2) (Sym',(IMAGE OUTR P'),S2'))))
       ``,
       rpt gen_tac >>      
     rewrite_tac[binterleave_ts,traces_def,comptraces_def,EXTENSION] >>
     FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [SUBSET_DEF] >>
     metis_tac[binterleave_trace_comp_to_decomp_generaldeduction_thm]   
  );

  
val binterleave_trace_decomp_to_comp_generaldeduction_thm = store_thm(
  "binterleave_trace_decomp_to_comp_generaldeduction",
  ``∀t Sym P S1 S2 Sym' P' S1' S2' (MTrn1:('event1 + 'eventS, 'pred1, 'state1, 'symb) mtrel) (MTrn2:('event2 + 'eventS, 'pred2, 'state2, 'symb) mtrel) (ded1:('pred1) tded) (ded2:('pred2) tded) (ded3:('pred1 + 'pred2) tded). 
       TransEnable ded3 (MTrn1,ded1) (MTrn2,ded2) ⇒
       ((∃t1 t2. (MTrn1 (Sym,(IMAGE OUTL P),S1) t1 (Sym',(IMAGE OUTL P'),S1')) ∧ (MTrn2 (Sym,(IMAGE OUTR P),S2) t2 (Sym',(IMAGE OUTR P'),S2')) ∧ (binterl t1 t2 t))
     ⇒
     (symbolicParlComp (MTrn1,ded1) (MTrn2,ded2) ded3 (Sym,P,S1,S2) t (Sym',P',S1',S2')))
     ``,
     GEN_TAC >>
     Induct_on `t` >-
      (rpt strip_tac >>
       IMP_RES_TAC binterl_Empty >>
       rw[]>>
       FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [symbolicParlComp_def] >>
       metis_tac[TranRelConfigEq,IMAGEOUT]) >>
     gen_tac >>
     reverse(Cases_on `h`) >-
      (Cases_on `x` >- (
        Cases_on `x'` >- 
         (FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [symbolicParlComp_def] >>
          rpt strip_tac >>
          IMP_RES_TAC binterl_moveAL >>
          rw[] >>
          IMP_RES_TAC TranRelSnocRevAsyncL >>
          Q.EXISTS_TAC `Sym''` >>
          Q.EXISTS_TAC `P''` >>
          Q.EXISTS_TAC `S1''` >>
          rw[]
          >- (metis_tac[TranRelConfigEq,IMAGEOUT]) >>
          PAT_X_ASSUM ``!Sym P S1 S2 Sym' P' S1' S2' MTrn1 MTrn2 ded1 ded2 ded3. A`` (ASSUME_TAC o (Q.SPECL [`Sym`,`P`,`S1`,`S2`,`Sym''`,`P''`,`S1''`,`S2'`,`MTrn1`,`MTrn2`,`ded1`,`ded2`,`ded3`])) >>
          IMP_RES_TAC binterl_movesL >>
          RES_TAC) >>
        FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [symbolicParlComp_def] >>
        rpt strip_tac >>
        IMP_RES_TAC binterl_moveSL >>
        rw[] >>
        IMP_RES_TAC TranRelSnocRevSync >>
        Q.EXISTS_TAC `Sym''`
        >>
        Q.EXISTS_TAC `P''` >>
        Q.EXISTS_TAC `S1''` >>
        Q.EXISTS_TAC `S2''` >>
        rw[] >>
        PAT_X_ASSUM ``!Sym P S1 S2 Sym' P' S1' S2' MTrn1 MTrn2 ded1 ded2 ded3. A`` (ASSUME_TAC o (Q.SPECL [`Sym`,`P`,`S1`,`S2`,`Sym''`,`P''`,`S1''`,`S2''`,`MTrn1`,`MTrn2`,`ded1`,`ded2`,`ded3`])) >>
        IMP_RES_TAC binterl_movesSL >>
        RES_TAC)
       >>
       Cases_on `y` >- (
        FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [symbolicParlComp_def] >>
        rpt strip_tac >>
        IMP_RES_TAC binterl_moveAR >>
        rw[] >>
        IMP_RES_TAC TranRelSnocRevAsyncR >>
        Q.EXISTS_TAC `Sym''`
        >>
        Q.EXISTS_TAC `P''` >>
        Q.EXISTS_TAC `S2''` >>
        rw[]
        >- ( metis_tac[TranRelConfigEq,IMAGEOUT]) >>
        PAT_X_ASSUM ``!Sym P S1 S2 Sym' P' S1' S2' MTrn1 MTrn2 ded1 ded2 ded3. A`` (ASSUME_TAC o (Q.SPECL [`Sym`,`P`,`S1`,`S2`,`Sym''`,`P''`,`S1'`,`S2''`,`MTrn1`,`MTrn2`,`ded1`,`ded2`,`ded3`])) >>
        IMP_RES_TAC binterl_movesR >>
        RES_TAC) >>
       FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [symbolicParlComp_def] >>
       rpt strip_tac >>
       IMP_RES_TAC binterl_moveSR >>
       rw[] >>
       IMP_RES_TAC TranRelSnocRevSync >>
       Q.EXISTS_TAC `Sym''` >>
       Q.EXISTS_TAC `P''` >>
       Q.EXISTS_TAC `S1''` >>
       Q.EXISTS_TAC `S2''` >>
       rw[] >>
       PAT_X_ASSUM ``!Sym P S1 S2 Sym' P' S1' S2' MTrn1 MTrn2 ded1 ded2 ded3. A`` (ASSUME_TAC o (Q.SPECL [`Sym`,`P`,`S1`,`S2`,`Sym''`,`P''`,`S1''`,`S2''`,`MTrn1`,`MTrn2`,`ded1`,`ded2`,`ded3`])) >>
       IMP_RES_TAC binterl_movesSR >>
       RES_TAC) >>
     FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [symbolicParlComp_def] >>
     rpt strip_tac >>
     IMP_RES_TAC TranRelSnocRevNone>>
     IMP_RES_TAC binterl_movecombinenone >>
     PAT_X_ASSUM ``!Sym P S1 S2 Sym' P' S1' S2' MTrn1 MTrn2 ded1 ded2 ded3. A`` (ASSUME_TAC o (Q.SPECL [`Sym`,`P`,`S1`,`S2`,`Sym'`,`P''`,`S1'`,`S2'`,`MTrn1`,`MTrn2`,`ded1`,`ded2`,`ded3`])) >>
     RES_TAC >>
     Q.EXISTS_TAC `P''` >>
     PAT_X_ASSUM ``!Ded1 Ded2 Ded3. A`` (ASSUME_TAC o (Q.SPECL [`ded1`,`ded2`,`ded3`]))  >>
     PAT_X_ASSUM ``!Ded1 Ded2 Ded3. A`` (ASSUME_TAC o (Q.SPECL [`ded1`,`ded2`,`ded3`]))  >>
     rw[TransEnable_def] 
  );


val binterleave_composition_generaldeduction_supseteq_thm = store_thm(
  "binterleave_composition_generaldeduction_supseteq",
  ``∀Sym P S1 S2 Sym' P' S1' S2' (MTrn1:('event1 + 'eventS, 'pred1, 'state1, 'symb) mtrel) (MTrn2:('event2 + 'eventS, 'pred2, 'state2, 'symb) mtrel) (Ded1:('pred1) tded) (Ded2:('pred2) tded) (ded3:('pred1 + 'pred2) tded).
         TransEnable ded3 (MTrn1,Ded1) (MTrn2,Ded2) ⇒
         ((binterleave_ts (traces (MTrn1,Ded1) (Sym,(IMAGE OUTL P),S1) (Sym',(IMAGE OUTL P'),S1')) (traces (MTrn2,Ded2) (Sym,(IMAGE OUTR P),S2) (Sym',(IMAGE OUTR P'),S2'))) ⊆
         (comptraces (MTrn1,Ded1) (MTrn2,Ded2) ded3 (Sym,P,S1,S2) (Sym',P',S1',S2')))
       ``,
         rpt gen_tac >>      
     rewrite_tac[binterleave_ts,traces_def,comptraces_def,EXTENSION] >>
     FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [SUBSET_DEF] >>
     metis_tac[binterleave_trace_decomp_to_comp_generaldeduction_thm]     
  );
  
 

val compose_vs_modules_generaldeduction_enable_disable_thm = store_thm(
  "compose_vs_modules_generaldeduction_enable_disable_thm",
  ``!Sym Sym' Sym'' Sym''' P P' P'' P''' S1 S1' S1'' S1''' S2 S2' S2'' S2''' (MTrn1:('event1 + 'eventS, 'pred1, 'state1, 'symb) mtrel) (MTrn1':('event1 + 'eventS, 'pred1, 'state1, 'symb) mtrel) (MTrn2:('event2 + 'eventS, 'pred2, 'state2, 'symb) mtrel) (MTrn2':('event2 + 'eventS, 'pred2, 'state2, 'symb) mtrel) (Ded1:('pred1) tded) (Ded1':('pred1) tded) (Ded2:('pred2) tded) (Ded2':('pred2) tded) (ded3:('pred1 + 'pred2) tded).
     (((traces (MTrn1,Ded1) (Sym,(IMAGE OUTL P),S1) (Sym',(IMAGE OUTL P'),S1')) ⊆ (traces (MTrn1',Ded1') (Sym'',(IMAGE OUTL P''),S1'') (Sym''',(IMAGE OUTL P'''),S1'''))) ∧
      ((traces (MTrn2,Ded2) (Sym,(IMAGE OUTR P),S2) (Sym',(IMAGE OUTR P'),S2')) ⊆ (traces (MTrn2',Ded2') (Sym'',(IMAGE OUTR P''),S2'') (Sym''',(IMAGE OUTR P'''),S2'''))) ∧
      (TransDisable ded3 (MTrn1,Ded1) (MTrn2,Ded2)) ∧
      (TransEnable ded3 (MTrn1',Ded1') (MTrn2',Ded2'))
 ) ==> ((comptraces (MTrn1,Ded1) (MTrn2,Ded2) ded3 (Sym,P,S1,S2) (Sym',P',S1',S2')) ⊆ (comptraces (MTrn1',Ded1') (MTrn2',Ded2') ded3 (Sym'',P'',S1'',S2'') (Sym''',P''',S1''',S2'''))) ``
  ,
rpt gen_tac >>      
rewrite_tac[binterleave_ts,traces_def,comptraces_def,EXTENSION] >>
FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [SUBSET_DEF] >>
rw[] >>
IMP_RES_TAC binterleave_trace_comp_to_decomp_generaldeduction_thm >>
PAT_X_ASSUM ``!t2. A`` (ASSUME_TAC o (Q.SPECL [`t2`])) >>
PAT_X_ASSUM ``!t1. A`` (ASSUME_TAC o (Q.SPECL [`t1`])) >>
RES_TAC >>
metis_tac[binterleave_trace_decomp_to_comp_generaldeduction_thm]
  );  



val _ = export_theory();
