open HolKernel Parse boolLib bossLib;
open rich_listTheory listTheory
open bir_expTheory HolBACoreSimps;
open bir_typing_expTheory bir_valuesTheory
open bir_envTheory bir_immTheory bir_imm_expTheory
open bir_immSyntax wordsTheory
open bir_mem_expTheory bir_bool_expTheory
open bir_exp_liftingTheory
open bir_temp_varsTheory

open arm8Theory;
open m0Theory

(* The lifting library is in principle able to lift
   machine code for multiple architectures. However,
   it needs instantiating for each architecture. This
   is provided by this library. *)

val _ = new_theory "bir_lifting_machines";


(*****************)
(* General stuff *)
(*****************)


(*--------------*)
(* Lifting Imms *)
(*--------------*)

val _ = Datatype `bir_machine_lifted_imm_t = BMLI bir_var_t ('ms -> bir_imm_t)`

val bir_machine_lifted_imm_OK_def = Define `bir_machine_lifted_imm_OK (BMLI v (lf : 'ms -> bir_imm_t)) <=>
(~(bir_is_temp_var_name (bir_var_name v))) /\
(!ms. BType_Imm (type_of_bir_imm (lf ms)) = (bir_var_type v))`;


val bir_machine_lifted_imm_def = Define `bir_machine_lifted_imm (BMLI v lf) bs ms <=>

(bir_env_read v bs.bst_environ = BVal_Imm (lf ms)) /\
(bir_env_var_is_declared bs.bst_environ (bir_temp_var T v))`;


val bir_machine_lifted_imm_OK_IMPLIES_NO_TEMP_VAR = store_thm ("bir_machine_lifted_imm_OK_IMPLIES_NO_TEMP_VAR",
  ``!v lf. bir_machine_lifted_imm_OK (BMLI v lf) ==>
               ~(bir_is_temp_var_name (bir_var_name v))``,
SIMP_TAC std_ss [bir_machine_lifted_imm_OK_def]);


val bir_machine_lifted_imm_INITIALISED = store_thm ("bir_machine_lifted_imm_INITIALISED",
  ``!v lf bs ms. bir_machine_lifted_imm_OK (BMLI v lf) ==>
                 bir_machine_lifted_imm (BMLI v lf) bs ms ==>
                 (bir_env_var_is_initialised bs.bst_environ v)``,
SIMP_TAC (std_ss++bir_TYPES_ss) [bir_machine_lifted_imm_def, bir_machine_lifted_imm_OK_def,
  bir_env_var_is_initialised_def,
  bir_var_name_def, bir_var_type_def, bir_env_read_NEQ_UNKNOWN,
  type_of_bir_val_def]);


val bir_machine_lifted_imm_DECLARED = store_thm ("bir_machine_lifted_imm_DECLARED",
  ``!v lf bs ms.
      bir_machine_lifted_imm (BMLI v lf) bs ms ==>
      (bir_env_var_is_declared bs.bst_environ v)``,

SIMP_TAC (std_ss++bir_TYPES_ss) [bir_machine_lifted_imm_def, bir_env_var_is_declared_def,
  bir_env_read_NEQ_UNKNOWN, bir_env_lookup_type_def]);


val bir_machine_lifted_imm_DECLARED_TEMP = store_thm ("bir_machine_lifted_imm_DECLARED_TEMP",
  ``!v ty lf bs ms use_temp.
       bir_machine_lifted_imm (BMLI v lf) bs ms ==>
       (bir_env_var_is_declared bs.bst_environ (bir_temp_var use_temp v))``,
Cases_on `use_temp` >- SIMP_TAC std_ss [bir_machine_lifted_imm_def] >>
REWRITE_TAC[bir_temp_var_REWRS] >>
METIS_TAC[bir_machine_lifted_imm_DECLARED]);


val bir_machine_lifted_imm_LIFTED = store_thm ("bir_machine_lifted_imm_LIFTED",
  ``!v lf bs ms. bir_machine_lifted_imm_OK (BMLI v lf) ==>
                 bir_machine_lifted_imm (BMLI v lf) bs ms ==>
                 (bir_is_lifted_exp bs.bst_environ (BExp_Den v) (BLV_Imm (lf ms)))
``,

SIMP_TAC (std_ss++bir_TYPES_ss) [bir_machine_lifted_imm_def,
  bir_machine_lifted_imm_OK_def,
  bir_is_lifted_exp_def, bir_is_lifted_imm_exp_def,
  bir_eval_exp_def, type_of_bir_exp_def,
  bir_var_type_def, bir_vars_of_exp_def,
  bir_env_vars_are_initialised_INSERT,
  bir_env_vars_are_initialised_EMPTY,
  bir_env_var_is_initialised_def,
  bir_env_read_NEQ_UNKNOWN, type_of_bir_val_def]);


val bir_machine_lifted_imms_def = Define `bir_machine_lifted_imms vl bs ms =
EVERY (\vlf. bir_machine_lifted_imm vlf bs ms) vl`;


(*-------------*)
(* Lifting Mem *)
(*-------------*)


val _ = Datatype `bir_machine_lifted_mem_t = BMLM bir_var_t ('ms -> 'a word -> 'b word)`

val bir_machine_lifted_mem_OK_def = Define `bir_machine_lifted_mem_OK (BMLM v (lf : 'ms -> 'a word -> 'b word)) <=>
  (?sa sb.
     (bir_var_type v = BType_Mem sa sb) /\
     (size_of_bir_immtype sa = (dimindex (:'a))) /\
     (size_of_bir_immtype sb = (dimindex (:'b))) /\
     (~(bir_is_temp_var_name (bir_var_name v))))`;


val bir_machine_lifted_mem_def = Define `bir_machine_lifted_mem (BMLM v lf) bs ms <=>

?sa sb mem_n. (bir_var_type v = BType_Mem sa sb) /\
(bir_env_read v bs.bst_environ = BVal_Mem sa sb mem_n) /\
(lf ms = (\a. n2w (mem_n (w2n a)))) /\
(bir_env_var_is_declared bs.bst_environ (bir_temp_var T v))`;


val bir_machine_lifted_mem_OK_IMPLIES_NO_TEMP_VAR = store_thm ("bir_machine_lifted_mem_OK_IMPLIES_NO_TEMP_VAR",
  ``!v lf. bir_machine_lifted_mem_OK (BMLM v lf) ==>
               ~(bir_is_temp_var_name (bir_var_name v))``,
SIMP_TAC std_ss [bir_machine_lifted_mem_OK_def, GSYM LEFT_FORALL_IMP_THM]);


val bir_machine_lifted_mem_INITIALISED = store_thm ("bir_machine_lifted_mem_INITIALISED",
  ``!v lf bs ms. bir_machine_lifted_mem_OK (BMLM v lf) ==>
                 bir_machine_lifted_mem (BMLM v lf) bs ms ==>
                 (bir_env_var_is_initialised bs.bst_environ v)``,
SIMP_TAC (std_ss++bir_TYPES_ss) [bir_machine_lifted_mem_def, bir_machine_lifted_mem_OK_def,
  bir_env_var_is_initialised_def,
  bir_var_name_def, bir_var_type_def, bir_env_read_NEQ_UNKNOWN,
  type_of_bir_val_def, GSYM LEFT_FORALL_IMP_THM]);


val bir_machine_lifted_mem_DECLARED = store_thm ("bir_machine_lifted_mem_DECLARED",
  ``!v lf bs ms.
      bir_machine_lifted_mem (BMLM v lf) bs ms ==>
      (bir_env_var_is_declared bs.bst_environ v)``,

SIMP_TAC (std_ss++bir_TYPES_ss) [bir_machine_lifted_mem_def, bir_env_var_is_declared_def,
  bir_env_read_NEQ_UNKNOWN, bir_env_lookup_type_def, GSYM LEFT_FORALL_IMP_THM]);


val bir_machine_lifted_mem_DECLARED_TEMP = store_thm ("bir_machine_lifted_mem_DECLARED_TEMP",
  ``!v ty lf bs ms use_temp.
       bir_machine_lifted_mem (BMLM v lf) bs ms ==>
       (bir_env_var_is_declared bs.bst_environ (bir_temp_var use_temp v))``,
Cases_on `use_temp` >- SIMP_TAC std_ss [bir_machine_lifted_mem_def, GSYM LEFT_FORALL_IMP_THM] >>
REWRITE_TAC[bir_temp_var_REWRS] >>
METIS_TAC[bir_machine_lifted_mem_DECLARED]);


val bir_machine_lifted_mem_LIFTED = store_thm ("bir_machine_lifted_mem_LIFTED",
  ``!v lf bs ms. bir_machine_lifted_mem_OK (BMLM v lf) ==>
                 bir_machine_lifted_mem (BMLM v lf) bs ms ==>
                 (bir_is_lifted_exp bs.bst_environ (BExp_Den v) (BLV_Mem (lf ms)))
``,

SIMP_TAC (std_ss++bir_TYPES_ss) [bir_machine_lifted_mem_def,
  bir_machine_lifted_mem_OK_def,
  bir_is_lifted_exp_def, bir_is_lifted_mem_exp_def,
  bir_eval_exp_def, type_of_bir_exp_def,
  bir_var_type_def, bir_vars_of_exp_def,
  bir_env_vars_are_initialised_INSERT,
  bir_env_vars_are_initialised_EMPTY,
  bir_env_var_is_initialised_def,
  bir_env_read_NEQ_UNKNOWN, type_of_bir_val_def,
  GSYM LEFT_FORALL_IMP_THM]);




(*----*)
(* PC *)
(*----*)


val _ = Datatype `bir_machine_lifted_pc_t = BMLPC bir_var_t bir_var_t ('ms -> bir_imm_t)`

val bir_machine_lifted_pc_OK_def = Define `bir_machine_lifted_pc_OK (BMLPC v_pc v_pc_cond (lf : 'ms -> bir_imm_t)) <=>
  (bir_is_temp_var_name (bir_var_name v_pc)) /\
  (bir_is_temp_var_name (bir_var_name v_pc_cond)) /\
  (!ms. BType_Imm (type_of_bir_imm (lf ms)) = (bir_var_type v_pc)) /\
  (bir_var_type v_pc_cond = BType_Bool)`;


val bir_machine_lifted_pc_def = Define `bir_machine_lifted_pc (BMLPC v_pc v_pc_cond lf) bs ms <=>

(bir_env_var_is_declared bs.bst_environ v_pc) /\
(bir_env_var_is_declared bs.bst_environ v_pc_cond) /\
(((bs.bst_pc = bir_block_pc (BL_Address (lf ms))) /\ (bs.bst_status = BST_Running)) \/
(bs.bst_status = BST_JumpOutside (BL_Address (lf ms))))`;


val bir_machine_lifted_pc_DECLARED = store_thm ("bir_machine_lifted_pc_DECLARED",
  ``!v_pc v_pc_cond lf bs ms.
      bir_machine_lifted_pc (BMLPC v_pc v_pc_cond lf) bs ms ==>
      (bir_env_var_is_declared bs.bst_environ v_pc) /\
      (bir_env_var_is_declared bs.bst_environ v_pc_cond)``,

SIMP_TAC (std_ss++bir_TYPES_ss) [bir_machine_lifted_pc_def]);



(***********************************************************)
(* A record linking a bir-state and the state of a machine *)
(***********************************************************)


val _ = Datatype `bir_lifting_machine_rec_t =
   <| (* a list of lifted immediate values *)
      bmr_imms : ('machine_state bir_machine_lifted_imm_t) list;

      (* The lifted memory *)
      bmr_mem : ('a, 'b, 'machine_state) bir_machine_lifted_mem_t;

      (* The PC *)
      bmr_pc : 'machine_state bir_machine_lifted_pc_t;

      (* Well formed state conditions, like we are in user mode ... *)
      bmr_extra : 'machine_state -> bool
   |>`;

val bmr_ss = rewrites (
   (type_rws ``:('a, 'b, 'c) bir_lifting_machine_rec_t``) @
   (type_rws ``:'a bir_machine_lifted_pc_t``) @
   (type_rws ``:'a bir_machine_lifted_imm_t``) @
   (type_rws ``:('a, 'b, 'c) bir_machine_lifted_mem_t``)
)
;


val bmr_ok_def = Define `bmr_ok r <=>
(EVERY bir_machine_lifted_imm_OK r.bmr_imms) /\
(bir_machine_lifted_mem_OK r.bmr_mem) /\
(bir_machine_lifted_pc_OK r.bmr_pc)`;


val bmr_rel_def = Define `bmr_rel r bs ms <=>
(EVERY (\i. bir_machine_lifted_imm i bs ms) r.bmr_imms) /\
(bir_machine_lifted_mem r.bmr_mem bs ms) /\
(bir_machine_lifted_pc r.bmr_pc bs ms) /\
(r.bmr_extra ms)`


val bmr_vars_def = Define `bmr_vars r =
  (case r.bmr_mem of (BMLM v _) => v)::
  (MAP (\i. case i of (BMLI v _) => v) r.bmr_imms)`;

val bmr_temp_vars_def = Define `bmr_temp_vars r =
  (case r.bmr_pc of BMLPC v1 v2 _ => [v1;v2]) ++
  (MAP (bir_temp_var T) (bmr_vars r))`;


val MEM_bmr_vars = store_thm ("MEM_bmr_vars",
``!r v. MEM v (bmr_vars r) <=> (?mf. r.bmr_mem = (BMLM v mf)) \/
                               (?lf. MEM (BMLI v lf) r.bmr_imms)``,

SIMP_TAC list_ss [bmr_vars_def, MEM_MAP] >>
REPEAT STRIP_TAC >> EQ_TAC >| [
  SIMP_TAC std_ss [DISJ_IMP_THM, PULL_EXISTS] >>
  CONJ_TAC >> REPEAT GEN_TAC >> REPEAT CASE_TAC >>
  METIS_TAC[],

  SIMP_TAC (std_ss++bmr_ss) [DISJ_IMP_THM, PULL_EXISTS] >>
  REPEAT STRIP_TAC >>
  DISJ2_TAC >>
  Q.EXISTS_TAC `BMLI v lf` >>
  ASM_SIMP_TAC (std_ss++bmr_ss) []
]);


val MEM_bmr_temp_vars = store_thm ("MEM_bmr_temp_vars",
``!r v. MEM v (bmr_temp_vars r) <=>

      (?v'. MEM v' (bmr_vars r) /\
            (v = bir_temp_var T v')) \/
      (?v_pc v_pc_cond lf. (r.bmr_pc = BMLPC v_pc v_pc_cond lf) /\
                           ((v = v_pc) \/ (v = v_pc_cond)))``,

SIMP_TAC list_ss [bmr_temp_vars_def, MEM_MAP] >>
REPEAT GEN_TAC >>
Cases_on `r.bmr_pc` >> rename1 `BMLPC v_pc v_pc_cond lf` >>
SIMP_TAC (list_ss++bmr_ss++boolSimps.EQUIV_EXTRACT_ss) [] >>
METIS_TAC[]);



val bmr_vars_NO_TEMP_VAR = store_thm ("bmr_vars_NO_TEMP_VAR",
  ``!r. bmr_ok r ==>
    EVERY (\v. ~(bir_is_temp_var_name (bir_var_name v))) (bmr_vars r)``,

SIMP_TAC list_ss [bmr_ok_def, EVERY_MEM, MEM_bmr_vars,
  DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS] >>
REPEAT STRIP_TAC >| [
  FULL_SIMP_TAC std_ss [bir_machine_lifted_mem_OK_def],

  `bir_machine_lifted_imm_OK (BMLI v lf)` by METIS_TAC[] >>
  FULL_SIMP_TAC std_ss [bir_machine_lifted_imm_OK_def]
])


val bmr_temp_vars_TEMP_VAR = store_thm ("bmr_temp_vars_TEMP_VAR",
  ``!r. bmr_ok r ==>
    EVERY (\v. (bir_is_temp_var_name (bir_var_name v))) (bmr_temp_vars r)``,

SIMP_TAC list_ss [bmr_ok_def, EVERY_MEM, MEM_bmr_temp_vars,
  DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS, bir_temp_var_REWRS,
  bir_is_temp_var_name_REWR] >>
REPEAT STRIP_TAC >> FULL_SIMP_TAC std_ss [bir_machine_lifted_pc_OK_def]);



val bmr_vars_IN_TEMP = store_thm ("bmr_vars_IN_TEMP",
``!r v. MEM v (bmr_vars r) ==> MEM (bir_temp_var T v) (bmr_temp_vars r)``,

SIMP_TAC list_ss [bmr_temp_vars_def, MEM_MAP] >>
METIS_TAC[]);


val bmr_vars_INITIALISED = store_thm ("bmr_vars_INITIALISED",
``!r bs ms. bmr_ok r ==> bmr_rel r bs ms ==>
   EVERY (bir_env_var_is_initialised bs.bst_environ) (bmr_vars r)``,

SIMP_TAC std_ss [bmr_ok_def, bmr_rel_def, EVERY_MEM, MEM_bmr_vars,
  DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS] >>
REPEAT STRIP_TAC >| [
  METIS_TAC[bir_machine_lifted_mem_INITIALISED],
  METIS_TAC[bir_machine_lifted_imm_INITIALISED]
]);


val bmr_vars_DECLARED = store_thm ("bmr_vars_DECLARED",
``!r bs ms. bmr_rel r bs ms ==>
   EVERY (bir_env_var_is_declared bs.bst_environ) (bmr_vars r)``,

SIMP_TAC std_ss [bmr_ok_def, bmr_rel_def, EVERY_MEM, MEM_bmr_vars,
  DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS] >>
REPEAT STRIP_TAC >| [
  METIS_TAC[bir_machine_lifted_mem_DECLARED],
  METIS_TAC[bir_machine_lifted_imm_DECLARED]
]);


val bmr_temp_vars_DECLARED = store_thm ("bmr_temp_vars_DECLARED",
``!r bs ms. bmr_rel r bs ms ==>
   EVERY (bir_env_var_is_declared bs.bst_environ) (bmr_temp_vars r)``,

SIMP_TAC std_ss [bmr_ok_def, bmr_rel_def, EVERY_MEM, MEM_bmr_temp_vars, MEM_bmr_vars,
  DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS] >>
REPEAT STRIP_TAC >| [
  METIS_TAC[bir_machine_lifted_mem_DECLARED_TEMP],
  METIS_TAC[bir_machine_lifted_imm_DECLARED_TEMP],
  METIS_TAC[bir_machine_lifted_pc_DECLARED],
  METIS_TAC[bir_machine_lifted_pc_DECLARED]
]);



(**********)
(* ARM 8  *)
(**********)

(* Lifting REGs *)

val arm8_REGS_lifted_imms_LIST_def = Define `
  arm8_REGS_lifted_imms_LIST =
    (MAP (\n. (BMLI (BVar (STRCAT "R" (n2s 10 HEX n)) (BType_Imm Bit64))
               (\ms:arm8_state. Imm64 (ms.REG (n2w n)))))  (COUNT_LIST 32))`;

val arm8_REGS_lifted_imms_LIST_EVAL = save_thm ("arm8_REGS_lifted_imms_LIST_EVAL",
  EVAL ``arm8_REGS_lifted_imms_LIST``);


(* Lifting PSTATE *)
val arm8_PSTATE_lifted_imms_LIST_def = Define `
  arm8_PSTATE_lifted_imms_LIST = [
    (BMLI (BVar "ProcState_C" BType_Bool) (\ms. bool2b (ms.PSTATE.C)));
    (BMLI (BVar "ProcState_N" BType_Bool) (\ms. bool2b (ms.PSTATE.N)));
    (BMLI (BVar "ProcState_V" BType_Bool) (\ms. bool2b (ms.PSTATE.V)));
    (BMLI (BVar "ProcState_Z" BType_Bool) (\ms:arm8_state. bool2b (ms.PSTATE.Z)))
]`;


(* Lifting special stuff *)
val arm8_EXTRA_lifted_imms_LIST_def = Define `
  arm8_EXTRA_lifted_imms_LIST = [
    (BMLI (BVar "SP_EL0" (BType_Imm Bit64)) (\ms:arm8_state. Imm64 (ms.SP_EL0)));
    (BMLI (BVar "SP_EL1" (BType_Imm Bit64)) (\ms. Imm64 (ms.SP_EL1)));
    (BMLI (BVar "SP_EL2" (BType_Imm Bit64)) (\ms. Imm64 (ms.SP_EL2)));
    (BMLI (BVar "SP_EL3" (BType_Imm Bit64)) (\ms. Imm64 (ms.SP_EL3)))
  ]`;


val arm8_lifted_mem_def = Define `
  arm8_lifted_mem = BMLM (BVar "MEM" (BType_Mem Bit64 Bit8)) (\ms:arm8_state. ms.MEM)`

val arm8_lifted_pc_def = Define `
  arm8_lifted_pc = BMLPC (BVar (bir_temp_var_name "PC") (BType_Imm Bit64))
                         (BVar (bir_temp_var_name "COND") BType_Bool)
                         (\ms:arm8_state. Imm64 (ms.PC))`

(* Well defined state *)
val arm8_state_is_OK_def = Define `arm8_state_is_OK (ms:arm8_state) <=> (
   ~ms.SCTLR_EL1.E0E ∧ (ms.PSTATE.EL = 0w) ∧ (ms.exception = NoException) /\
   ~ms.SCTLR_EL1.SA0 /\
   ~ms.TCR_EL1.TBI0 /\
   ~ms.TCR_EL1.TBI1)`

val arm8_bmr_def = Define `arm8_bmr = <|
  bmr_extra := \ms. arm8_state_is_OK ms;
  bmr_imms := (arm8_REGS_lifted_imms_LIST ++ arm8_PSTATE_lifted_imms_LIST ++ arm8_EXTRA_lifted_imms_LIST);
  bmr_mem := arm8_lifted_mem;
  bmr_pc := arm8_lifted_pc |>`;

val arm8_bmr_EVAL = save_thm ("arm8_bmr_EVAL",
  SIMP_CONV list_ss [arm8_bmr_def, arm8_state_is_OK_def,
    arm8_REGS_lifted_imms_LIST_EVAL, arm8_PSTATE_lifted_imms_LIST_def,
    arm8_EXTRA_lifted_imms_LIST_def, arm8_lifted_mem_def,
    arm8_lifted_pc_def, bir_temp_var_name_def, arm8_state_is_OK_def]
    ``arm8_bmr``
);



val arm8_bmr_OK = store_thm ("arm8_bmr_OK",
  ``bmr_ok arm8_bmr``,

SIMP_TAC (list_ss++bmr_ss++stringSimps.STRING_ss++wordsLib.WORD_ss++holBACore_ss) [
  bmr_ok_def, arm8_bmr_EVAL,
  bir_machine_lifted_mem_OK_def, bir_machine_lifted_imm_OK_def,
  bir_is_temp_var_name_def, BType_Bool_def,
  bir_machine_lifted_pc_OK_def]);

val arm8_bmr_rel_EVAL = save_thm ("arm8_bmr_rel_EVAL",
SIMP_CONV (list_ss++bmr_ss++holBACore_ss) [
  bmr_rel_def, arm8_bmr_EVAL,
  bir_machine_lifted_mem_def, bir_machine_lifted_imm_def,
  bir_is_temp_var_name_def, BType_Bool_def, bir_temp_var_name_def,
  bir_machine_lifted_pc_def, bir_temp_var_def,
  GSYM CONJ_ASSOC]
``bmr_rel arm8_bmr bs ms``);


val arm8_brm_vars_EVAL = save_thm ("arm8_brm_vars_EVAL",
SIMP_CONV (list_ss++bmr_ss) [arm8_bmr_EVAL, bmr_vars_def] ``bmr_vars arm8_bmr``);

val arm8_brm_temp_vars_EVAL = save_thm ("arm8_brm_temp_vars_EVAL",
SIMP_CONV (list_ss++bmr_ss) [arm8_bmr_EVAL, bmr_vars_def, bmr_temp_vars_def,
  bir_temp_var_def, bir_temp_var_name_def] 
  ``bmr_temp_vars arm8_bmr``);



(**********)
(* ARM M0 *)
(**********)

(* Lifting REGs *)
val m0_REGS_lifted_imms_LIST_def = Define `
  m0_REGS_lifted_imms_LIST = [
    (BMLI (BVar "R0" (BType_Imm Bit32)) (\ms. Imm32 (ms.REG RName_0)));
    (BMLI (BVar "R1" (BType_Imm Bit32)) (\ms. Imm32 (ms.REG RName_1)));
    (BMLI (BVar "R2" (BType_Imm Bit32)) (\ms. Imm32 (ms.REG RName_2)));
    (BMLI (BVar "R3" (BType_Imm Bit32)) (\ms. Imm32 (ms.REG RName_3)));
    (BMLI (BVar "R4" (BType_Imm Bit32)) (\ms. Imm32 (ms.REG RName_4)));
    (BMLI (BVar "R5" (BType_Imm Bit32)) (\ms. Imm32 (ms.REG RName_5)));
    (BMLI (BVar "R6" (BType_Imm Bit32)) (\ms. Imm32 (ms.REG RName_6)));
    (BMLI (BVar "R7" (BType_Imm Bit32)) (\ms. Imm32 (ms.REG RName_7)));
    (BMLI (BVar "R8" (BType_Imm Bit32)) (\ms. Imm32 (ms.REG RName_8)));
    (BMLI (BVar "R9" (BType_Imm Bit32)) (\ms. Imm32 (ms.REG RName_9)));
    (BMLI (BVar "R10" (BType_Imm Bit32)) (\ms. Imm32 (ms.REG RName_10)));
    (BMLI (BVar "R11" (BType_Imm Bit32)) (\ms. Imm32 (ms.REG RName_11)));
    (BMLI (BVar "R12" (BType_Imm Bit32)) (\ms. Imm32 (ms.REG RName_12)));
    (BMLI (BVar "LR" (BType_Imm Bit32)) (\ms. Imm32 (ms.REG RName_LR)));
    (BMLI (BVar "SP_main" (BType_Imm Bit32)) (\ms. Imm32 (ms.REG RName_SP_main)));
    (BMLI (BVar "SP_process" (BType_Imm Bit32)) (\ms. Imm32 (ms.REG RName_SP_process)))]`;


val m0_lifted_mem_def = Define `
  m0_lifted_mem = BMLM (BVar "MEM" (BType_Mem Bit32 Bit8)) (\ms:m0_state. ms.MEM)`

val m0_lifted_pc_def = Define `
  m0_lifted_pc = BMLPC (BVar (bir_temp_var_name "PC") (BType_Imm Bit32))
                       (BVar (bir_temp_var_name "COND") BType_Bool)
                       (\ms:m0_state. Imm32 (ms.REG RName_PC))`


(* Just a dummy for now *)
val m0_bmr_def = Define `m0_bmr = <|
  bmr_extra := \ms:m0_state. T;
  bmr_imms := m0_REGS_lifted_imms_LIST;
  bmr_mem := m0_lifted_mem;
  bmr_pc := m0_lifted_pc |>`;

val m0_bmr_EVAL = save_thm ("m0_bmr_EVAL",
  SIMP_CONV list_ss [m0_bmr_def,
    m0_REGS_lifted_imms_LIST_def, m0_lifted_mem_def,
    m0_lifted_pc_def, bir_temp_var_name_def, arm8_state_is_OK_def]
    ``m0_bmr``
);

val m0_bmr_OK = store_thm ("m0_bmr_OK",
  ``bmr_ok m0_bmr``,

SIMP_TAC (list_ss++bmr_ss++stringSimps.STRING_ss++wordsLib.WORD_ss++holBACore_ss) [
  bmr_ok_def, m0_bmr_EVAL,
  bir_machine_lifted_mem_OK_def, bir_machine_lifted_imm_OK_def,
  bir_is_temp_var_name_def, BType_Bool_def,
  bir_machine_lifted_pc_OK_def]);


val _ = export_theory();
