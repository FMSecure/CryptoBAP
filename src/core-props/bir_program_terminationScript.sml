open HolKernel Parse boolLib bossLib;
open bir_programTheory bir_program_valid_stateTheory HolBACoreSimps;
open bir_program_multistep_propsTheory bir_auxiliaryTheory
open bir_valuesTheory bir_immTheory

val _ = new_theory "bir_program_termination";


(* ------------------------------------------------------------------------- *)
(* This theory tries to reason about which possible ways there are for a     *)
(* program to terminate                                                      *)
(* ------------------------------------------------------------------------- *)


(***************************************)
(* Termination changes just the status *)
(***************************************)

(* If we are in a non-terminated state, execute a statement and
   terminate, then only the status was changed. Otherwise the state
   stays unchanged, including the PC and all the values. This means
   that we can easily examine which statement went wrong. *)

(* The property holds for basic statements *)
val bir_exec_stmtB_terminates_no_change = store_thm ("bir_exec_stmtB_terminates_no_change",
``!st stmt fe st'.
     ~(bir_state_is_terminated st) ==>
     (bir_exec_stmtB stmt st = (fe, st')) ==>
     (bir_state_is_terminated st') ==>
     (((st' with bst_status := BST_Running) = st) /\ (fe = NONE))``,

SIMP_TAC (std_ss++holBACore_ss) [bir_state_is_terminated_def,
  bir_state_t_component_equality, bir_exec_stmtB_pc_unchanged] >>
Cases_on `stmt` >> (
  SIMP_TAC std_ss [bir_exec_stmtB_def, LET_DEF,
    bir_exec_stmt_declare_def, bir_exec_stmt_assume_def,
    bir_exec_stmt_assign_def, bir_exec_stmt_assert_def,
    bir_exec_stmt_observe_def] >>
  REPEAT GEN_TAC >> STRIP_TAC >>
  REPEAT CASE_TAC >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_state_set_failed_def,
    bir_state_is_terminated_def, bir_state_t_component_equality]
));

val bir_exec_stmtB_terminates_no_change_state = store_thm ("bir_exec_stmtB_terminates_no_change_state",
``!st stmt. ~(bir_state_is_terminated st) ==>
              (bir_state_is_terminated (bir_exec_stmtB_state stmt st)) ==>
              (((bir_exec_stmtB_state stmt st) with bst_status := BST_Running) = st)``,

REPEAT STRIP_TAC >>
Cases_on `bir_exec_stmtB stmt st` >>
FULL_SIMP_TAC std_ss [bir_exec_stmtB_state_def] >>
METIS_TAC[bir_exec_stmtB_terminates_no_change]);


(* And for end statements *)
val bir_exec_stmtE_terminates_no_change = store_thm ("bir_exec_stmtE_terminates_no_change",
``!p st stmt. ~(bir_state_is_terminated st) ==>
              (bir_state_is_terminated (bir_exec_stmtE p stmt st)) ==>
              (((bir_exec_stmtE p stmt st) with bst_status := BST_Running) = st)``,

SIMP_TAC (std_ss++holBACore_ss) [bir_state_is_terminated_def,
  bir_state_t_component_equality, bir_exec_stmtB_pc_unchanged] >>
Cases_on `stmt` >> (
  SIMP_TAC std_ss [bir_exec_stmtE_def, LET_DEF, bir_exec_stmt_cjmp_def,
    bir_exec_stmt_jmp_def, bir_exec_stmt_jmp_to_label_def, bir_exec_stmt_halt_def] >>
  REPEAT GEN_TAC >> STRIP_TAC >>
  REPEAT CASE_TAC >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_state_set_failed_def]
));


(* Thus it holds for all statements. *)
val bir_exec_stmt_terminates_no_change = store_thm ("bir_exec_stmt_terminates_no_change",
``!p st (stmt:'a bir_stmt_t) fe st'. ~(bir_state_is_terminated st) ==>
              (bir_exec_stmt p stmt st = (fe, st')) ==>
              (bir_state_is_terminated st') ==>
              (((st' with bst_status := BST_Running) = st) /\ (fe = NONE))``,

Cases_on `stmt:'a bir_stmt_t` >| [
  REPEAT GEN_TAC >> REPEAT DISCH_TAC >>
  rename1 `BStmtB (stmtB:'a bir_stmt_basic_t)` >>
  MP_TAC (Q.SPECL [`st`, `stmtB:'a bir_stmt_basic_t`] bir_exec_stmtB_terminates_no_change) >>
  `?fe' st''. bir_exec_stmtB stmtB st = (fe', st'')` by METIS_TAC[pairTheory.PAIR] >>
  ASM_SIMP_TAC std_ss [] >>
  Cases_on `st''.bst_status = BST_Running` >> (
    FULL_SIMP_TAC (std_ss++holBACore_ss) [
      bir_exec_stmt_def, LET_DEF, bir_state_is_terminated_def,
      bir_state_t_component_equality]
  ),

  SIMP_TAC std_ss [bir_exec_stmt_def, bir_exec_stmtE_terminates_no_change]
]);


val bir_exec_stmt_terminates_no_change_state = store_thm ("bir_exec_stmt_terminates_no_change_state",
``!p st (stmt:'a bir_stmt_t). ~(bir_state_is_terminated st) ==>
              (bir_state_is_terminated (bir_exec_stmt_state p stmt st)) ==>
             (((bir_exec_stmt_state p stmt st) with bst_status := BST_Running) = st)``,

REPEAT STRIP_TAC >>
Cases_on `bir_exec_stmt p stmt st` >>
FULL_SIMP_TAC std_ss [bir_exec_stmt_state_def] >>
METIS_TAC[bir_exec_stmt_terminates_no_change]);


(* It holds for single steps *)
val bir_exec_step_terminates_no_change = store_thm ("bir_exec_step_terminates_no_change",
``!p st fe st'. ~(bir_state_is_terminated st) ==>
              (bir_exec_step p st = (fe, st')) ==>
              (bir_state_is_terminated st') ==>
              (((st' with bst_status := BST_Running) = st) /\ (fe = NONE))``,

SIMP_TAC std_ss [bir_exec_step_def] >>
REPEAT GEN_TAC >> REPEAT DISCH_TAC >>
Cases_on `bir_get_current_statement p st.bst_pc` >| [
  FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_state_set_failed_def, bir_state_is_terminated_def,
    bir_state_t_component_equality],

  FULL_SIMP_TAC std_ss [] >>
  METIS_TAC[bir_exec_stmt_terminates_no_change]
]);


val bir_exec_step_terminates_no_change_state = store_thm (
"bir_exec_step_terminates_no_change_state",
``!p st. ~(bir_state_is_terminated st) ==>
         (bir_state_is_terminated (bir_exec_step_state p st)) ==>
         (((bir_exec_step_state p st) with bst_status := BST_Running) = st)``,

REPEAT STRIP_TAC >>
Cases_on `bir_exec_step p st` >>
FULL_SIMP_TAC std_ss [bir_exec_step_state_def] >>
METIS_TAC[bir_exec_step_terminates_no_change]);



(* We can iterate with same effect *)
val bir_exec_step_n_last_step_terminates = store_thm ("bir_exec_step_n_last_step_terminates",
``!p st n st' l i.
     (bir_exec_step_n p st n = (l, SUC i, st')) ==>
     (bir_state_is_terminated st') ==> (
     ?st''. (bir_exec_step_n p st i = (l, i, st'')) /\
            (st'' = st' with bst_status := BST_Running) /\
            (bir_exec_step p st'' = (NONE, st')))``,

REPEAT STRIP_TAC >>
`bir_exec_step_n p st (SUC i) = (l, SUC i, st')` by METIS_TAC[bir_exec_step_n_LIMIT_STEP_NO] >>
`(?l' c' st''. bir_exec_step_n p st i = (l', c', st''))` by
  METIS_TAC[pairTheory.PAIR] >>
`c' <= i` by FULL_SIMP_TAC std_ss [bir_exec_step_n_EQ_THM] >>
FULL_SIMP_TAC std_ss [bir_exec_step_n_SUC_END, LET_DEF] >>
Cases_on `bir_state_is_terminated st''` >> (
  FULL_SIMP_TAC arith_ss []
) >>
`?fe st'''. bir_exec_step p st'' = (fe, st''')` by
  METIS_TAC[pairTheory.PAIR] >>
FULL_SIMP_TAC std_ss [] >>
REPEAT BasicProvers.VAR_EQ_TAC >>
`(fe = NONE) /\ (st'' = (st' with bst_status := BST_Running))` by
  METIS_TAC[bir_exec_step_terminates_no_change] >>
FULL_SIMP_TAC list_ss [OPT_CONS_REWRS]);




(*****************)
(* Status Halted *)
(*****************)

val bir_exec_stmtB_status_not_halted = store_thm ("bir_exec_stmtB_status_not_halted",
``!st stmt v. (st.bst_status <> BST_Halted v) ==> (((bir_exec_stmtB_state stmt st).bst_status <> BST_Halted v))``,

Cases_on `stmt` >> (
  ASM_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_stmtB_state_REWRS, LET_DEF,
    bir_exec_stmt_declare_def, bir_exec_stmt_assume_def,
    bir_exec_stmt_assign_def, bir_exec_stmt_assert_def,
    bir_exec_stmt_observe_state_def, bir_state_set_failed_def] >>
  REPEAT GEN_TAC >>
  REPEAT CASE_TAC >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) []
));


val bir_exec_stmtE_status_halted = store_thm ("bir_exec_stmtE_status_halted",
``!st p stmt v. (st.bst_status <> BST_Halted v) ==> (((bir_exec_stmtE p stmt st).bst_status = BST_Halted v)) ==> (?e. (stmt = BStmt_Halt e) /\ (v = bir_eval_exp e st.bst_environ))``,

Cases_on `stmt` >> (
  ASM_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_stmtE_def,
    bir_exec_stmt_jmp_def, bir_state_set_failed_def, bir_exec_stmt_jmp_to_label_def,
    bir_exec_stmt_cjmp_def, bir_exec_stmt_halt_def] >>
  REPEAT GEN_TAC >>
  REPEAT CASE_TAC >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) []
));



val bir_exec_stmt_status_halted = store_thm ("bir_exec_stmt_status_halted",
``!st p stmt v. (st.bst_status <> BST_Halted v) ==> (((bir_exec_stmt_state p stmt st).bst_status = BST_Halted v)) ==> (?e. (stmt = BStmtE (BStmt_Halt e)) /\ (v = bir_eval_exp e st.bst_environ))``,

Cases_on `stmt` >| [
  SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss++holBACore_ss) [bir_exec_stmt_state_REWRS, LET_DEF] >>
  METIS_TAC[bir_exec_stmtB_status_not_halted],

  SIMP_TAC (std_ss++holBACore_ss) [bir_exec_stmt_state_REWRS] >>
  METIS_TAC[bir_exec_stmtE_status_halted]
]);


val bir_exec_step_status_halted = store_thm ("bir_exec_step_status_halted",
``!st p v. (st.bst_status <> BST_Halted v) ==> (((bir_exec_step_state p st).bst_status = BST_Halted v)) ==> (?e. ((bir_get_current_statement p st.bst_pc = SOME (BStmtE (BStmt_Halt e)))) /\ (v = bir_eval_exp e st.bst_environ))``,

REPEAT GEN_TAC >>
SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss) [bir_exec_step_state_def, bir_exec_step_def] >>
CASE_TAC >> (
  ASM_SIMP_TAC (std_ss++holBACore_ss) [bir_state_set_failed_def, GSYM bir_exec_stmt_state_def]
) >>
METIS_TAC[bir_exec_stmt_status_halted]);



(**********************)
(* Status JumpOutside *)
(**********************)

val bir_exec_stmtB_status_not_jumped = store_thm ("bir_exec_stmtB_status_not_jumped",
``!st stmt l. (st.bst_status <> BST_JumpOutside l) ==> (((bir_exec_stmtB_state stmt st).bst_status <> BST_JumpOutside l))``,

Cases_on `stmt` >> (
  ASM_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_stmtB_state_REWRS, LET_DEF,
    bir_exec_stmt_declare_def, bir_exec_stmt_assume_def,
    bir_exec_stmt_assign_def, bir_exec_stmt_assert_def,
    bir_exec_stmt_observe_state_def, bir_state_set_failed_def] >>
  REPEAT GEN_TAC >>
  REPEAT CASE_TAC >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) []
));


val bir_stmtE_is_jmp_to_label_def = Define `bir_stmtE_is_jmp_to_label env l stmt <=>
                ((?le. (stmt = BStmt_Jmp le) /\ (bir_eval_label_exp le env = SOME l)) \/
                 (?le1 le2 ce c. (stmt = BStmt_CJmp ce le1 le2) /\
                                 (bir_eval_exp ce env = BVal_Imm (bool2b c)) /\
                                 (bir_eval_label_exp (if c then le1 else le2) env = SOME l)))`;

val bir_stmtE_is_jmp_to_label_REWRS = store_thm ("bir_stmtE_is_jmp_to_label_REWRS",
  ``(!le env l. (bir_stmtE_is_jmp_to_label env l (BStmt_Jmp le) <=>
       (bir_eval_label_exp le env = SOME l))) /\
    (!ce le1 le2 env l. (bir_stmtE_is_jmp_to_label env l (BStmt_CJmp ce le1 le2) <=>
       case (bir_dest_bool_val (bir_eval_exp ce env)) of
         | NONE => F
         | SOME T => (bir_eval_label_exp le1 env = SOME l)
         | SOME F => (bir_eval_label_exp le2 env = SOME l)
    )) /\
    (!l env e. (bir_stmtE_is_jmp_to_label env l (BStmt_Halt e) <=> F))``,

SIMP_TAC (std_ss++holBACore_ss) [bir_stmtE_is_jmp_to_label_def] >>
REPEAT GEN_TAC >> EQ_TAC >- (
  STRIP_TAC >>
  ASM_SIMP_TAC (std_ss++holBACore_ss) []  >>
  METIS_TAC[]
) >>
REPEAT CASE_TAC >>
FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_dest_bool_val_EQ_SOME] >> METIS_TAC[]);


val bir_stmtE_is_jmp_to_label_SEM = store_thm ("bir_stmtE_is_jmp_to_label_SEM",
  ``!p stmt st l. (bir_stmtE_is_jmp_to_label st.bst_environ l stmt) ==>
                  (bir_exec_stmtE p stmt st = bir_exec_stmt_jmp_to_label p l st)``,

Cases_on `stmt` >>
SIMP_TAC std_ss [bir_stmtE_is_jmp_to_label_REWRS, bir_exec_stmtE_def,
  bir_exec_stmt_jmp_def, bir_exec_stmt_cjmp_def] >>
REPEAT GEN_TAC >>
REPEAT CASE_TAC);



val bir_exec_stmtE_status_jumped = store_thm ("bir_exec_stmtE_status_jumped",
``!st p stmt l. (st.bst_status <> BST_JumpOutside l) ==>
                (((bir_exec_stmtE p stmt st).bst_status = BST_JumpOutside l)) ==>
                ((~(MEM l (bir_labels_of_program p))) /\
                 (bir_stmtE_is_jmp_to_label st.bst_environ l stmt))``,

Cases_on `stmt` >> (
  ASM_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_stmtE_def,
    bir_exec_stmt_jmp_def, bir_state_set_failed_def, bir_exec_stmt_jmp_to_label_def,
    bir_exec_stmt_cjmp_def, bir_exec_stmt_halt_def, bir_stmtE_is_jmp_to_label_REWRS] >>
  REPEAT GEN_TAC >>
  REPEAT CASE_TAC >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) [] >>
  METIS_TAC[]
));


val bir_stmt_is_jmp_to_label_def = Define `
  (bir_stmt_is_jmp_to_label env l (BStmtB _) <=> F) /\
  (bir_stmt_is_jmp_to_label env l (BStmtE stmt) = bir_stmtE_is_jmp_to_label env l stmt)`


val bir_stmt_is_jmp_to_label_SEM = store_thm ("bir_stmt_is_jmp_to_label_SEM",
  ``!p stmt st l. (bir_stmt_is_jmp_to_label st.bst_environ l stmt) ==>
                  (bir_exec_stmt p stmt st = (NONE, bir_exec_stmt_jmp_to_label p l st))``,

Cases_on `stmt` >>
SIMP_TAC std_ss [bir_stmt_is_jmp_to_label_def, bir_exec_stmt_def,
  bir_stmtE_is_jmp_to_label_SEM]);


val bir_exec_stmt_status_jumped = store_thm ("bir_exec_stmt_status_jumped",
``!st p stmt l. (st.bst_status <> BST_JumpOutside l) ==>
                (((bir_exec_stmt_state p stmt st).bst_status = BST_JumpOutside l)) ==>
                (~(MEM l (bir_labels_of_program p)) /\
                (bir_stmt_is_jmp_to_label st.bst_environ l stmt))``,

Cases_on `stmt` >| [
  SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss++holBACore_ss) [bir_exec_stmt_state_REWRS, LET_DEF] >>
  METIS_TAC[bir_exec_stmtB_status_not_jumped],

  SIMP_TAC std_ss [bir_exec_stmt_state_REWRS, bir_stmt_is_jmp_to_label_def] >>
  METIS_TAC[bir_exec_stmtE_status_jumped]
]);


val bir_exec_step_status_jumped = store_thm ("bir_exec_step_status_jumped",
``!st p l. (st.bst_status <> BST_JumpOutside l) ==>
           (((bir_exec_step_state p st).bst_status = BST_JumpOutside l)) ==>

                (~(MEM l (bir_labels_of_program p)) /\
                ((?stmt. (bir_get_current_statement p st.bst_pc = SOME stmt) /\
                         (bir_stmt_is_jmp_to_label st.bst_environ l stmt))))``,

REPEAT GEN_TAC >>
SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss) [bir_exec_step_state_def, bir_exec_step_def] >>
CASE_TAC >> (
  ASM_SIMP_TAC (std_ss++holBACore_ss) [bir_state_set_failed_def, GSYM bir_exec_stmt_state_def]
) >>
METIS_TAC[bir_exec_stmt_status_jumped]);


val bir_exec_step_n_status_jumped = store_thm ("bir_exec_step_n_status_jumped",
``!st p n l ol n' st'.
           (bir_exec_step_n p st n = (ol, SUC n', st')) ==>
           (st'.bst_status = BST_JumpOutside l) ==>
           ((~(MEM l (bir_labels_of_program p))) /\

           (?stmt. (bir_get_current_statement p st'.bst_pc = SOME stmt) /\
                   (bir_stmt_is_jmp_to_label st'.bst_environ l stmt)) /\
           (?st''. (bir_exec_step_n p st n' = (ol, n', st'')) /\
             (st'' = st' with bst_status := BST_Running) /\
             (bir_exec_step p st'' = (NONE, st'))))``,

REPEAT GEN_TAC >> REPEAT DISCH_TAC >>
MP_TAC (Q.SPECL [`p`, `st`, `n`] bir_exec_step_n_last_step_terminates) >>
ASM_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_state_is_terminated_def] >>
STRIP_TAC >>
MP_TAC (Q.SPECL [`st' with bst_status := BST_Running`, `p`] bir_exec_step_status_jumped) >>
ASM_SIMP_TAC (std_ss++bir_TYPES_ss) [bir_exec_step_state_def]);


(*****************************)
(* Status AssumptionViolated *)
(*****************************)


val bir_exec_stmtB_status_assumption = store_thm ("bir_exec_stmtB_status_assumption",
``!st stmt. (st.bst_status <> BST_AssumptionViolated) ==>
            ((bir_exec_stmtB_state stmt st).bst_status = BST_AssumptionViolated) ==>
            (?e. (stmt = BStmt_Assume e) /\ (bir_eval_exp e st.bst_environ = BVal_Imm (Imm1 0w)))``,

Cases_on `stmt` >> (
  ASM_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_stmtB_state_REWRS, LET_DEF,
    bir_exec_stmt_declare_def, bir_exec_stmt_assume_def,
    bir_exec_stmt_assign_def, bir_exec_stmt_assert_def,
    bir_exec_stmt_observe_state_def, bir_state_set_failed_def] >>
  REPEAT GEN_TAC >>
  REPEAT CASE_TAC >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) []
));


val bir_exec_stmtE_status_not_assumption = store_thm ("bir_exec_stmtE_status_not_assumption",
``!st p stmt. (st.bst_status <> BST_AssumptionViolated) ==>
              ~((bir_exec_stmtE p stmt st).bst_status = BST_AssumptionViolated)``,

Cases_on `stmt` >> (
  ASM_SIMP_TAC (std_ss++holBACore_ss) [bir_exec_stmtE_def,
    bir_exec_stmt_jmp_def, bir_state_set_failed_def, bir_exec_stmt_jmp_to_label_def,
    bir_exec_stmt_cjmp_def, bir_exec_stmt_halt_def, bir_stmtE_is_jmp_to_label_REWRS] >>
  REPEAT GEN_TAC >>
  REPEAT CASE_TAC >>
  FULL_SIMP_TAC (std_ss++holBACore_ss) []
));


val bir_exec_stmt_status_assumption = store_thm ("bir_exec_stmt_status_assumption",
``!st p stmt. (st.bst_status <> BST_AssumptionViolated) ==>
              (((bir_exec_stmt_state p stmt st).bst_status = BST_AssumptionViolated)) ==>
              (?e. (stmt = BStmtB (BStmt_Assume e)) /\ (bir_eval_exp e st.bst_environ = BVal_Imm (Imm1 0w)))``,

Cases_on `stmt` >| [
  SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss++holBACore_ss) [
    bir_exec_stmt_state_REWRS, LET_DEF] >>
  METIS_TAC[bir_exec_stmtB_status_assumption],

  SIMP_TAC (std_ss++holBACore_ss) [bir_exec_stmt_state_REWRS] >>
  METIS_TAC[bir_exec_stmtE_status_not_assumption]
]);


val bir_exec_step_status_assumption = store_thm ("bir_exec_step_status_assumption",
``!st p. (st.bst_status <> BST_AssumptionViolated) ==>
         ((bir_exec_step_state p st).bst_status = BST_AssumptionViolated) ==>
         (?e. (bir_get_current_statement p st.bst_pc = SOME (BStmtB (BStmt_Assume e))) /\
              (bir_eval_exp e st.bst_environ = BVal_Imm (Imm1 0w)))``,

REPEAT GEN_TAC >>
SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss) [bir_exec_step_state_def, bir_exec_step_def] >>
CASE_TAC >> (
  ASM_SIMP_TAC (std_ss++holBACore_ss) [bir_state_set_failed_def, GSYM bir_exec_stmt_state_def]
) >>
METIS_TAC[bir_exec_stmt_status_assumption]);



val _ = export_theory();
