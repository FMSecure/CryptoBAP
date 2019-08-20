(* Code specific for the example *)
open HolKernel Parse boolLib bossLib;
open bir_expSimps;
open tutorial_bir_to_armSupportTheory;
open bslSyntax;

(* unsigned comparison *)
EVAL ``255w <=+ (0w:word8)``;
(* Signed comparison *)
EVAL ``255w <= (0w:word8)``;

(* register add *)
val y_var = ``(m.REG 5w)``;
val x_var = ``(m.REG 4w)``;
val ly_var = ``(m.REG 3w)``;
val lx_var = ``(m.REG 2w)``;

val arm8_add_reg_pre_def = Define `arm8_add_reg_pre m =
  ((^x_var) >= 0w)
`;
val arm8_add_reg_post_def = Define `arm8_add_reg_post m =
  ((^x_var+^y_var) = (^ly_var))
`;

val get_y = bden (bvar "R5" ``(BType_Imm Bit64)``);
val get_x = bden (bvar "R4" ``(BType_Imm Bit64)``);
val get_ly = bden (bvar "R3" ``(BType_Imm Bit64)``);
val get_lx = bden (bvar "R2" ``(BType_Imm Bit64)``);


val bir_add_reg_pre_def = Define `bir_add_reg_pre =
^(bandl[
        bnot (bslt(get_x, bconst64 0)),
        beq(get_lx, get_x),
         beq(get_ly, get_y)
         ]
)
`;

val bir_add_reg_post_def = Define `bir_add_reg_post =
^(beq (bplus(get_y, get_x), get_ly))`;


val original_add_reg_loop_condition = 
 (bnot (bsle(get_lx, bconst64 0)));
val bir_add_reg_loop_condition =  bnot ``(BExp_BinExp BIExp_Or
                       (BExp_UnaryExp BIExp_Not
                          (BExp_BinPred BIExp_Equal
                             (BExp_Den (BVar "ProcState_N" BType_Bool))
                             (BExp_Den (BVar "ProcState_V" BType_Bool))))
                       (BExp_Den (BVar "ProcState_Z" BType_Bool)))``;


val bir_add_reg_I_def = Define `bir_add_reg_I =
^(bandl [
      (beq (bplus(get_y, get_x), bplus(get_ly, get_lx))),
   (beq (original_add_reg_loop_condition, bir_add_reg_loop_condition))
   ])
`;


(* contract one *)
(* from function entry (we avoid stack pointer operations) to cjmp *)
val bir_add_reg_contract_1_pre_def = Define `bir_add_reg_contract_1_pre =
 (bir_add_reg_pre)
`;
val bir_add_reg_contract_1_post_def = Define `bir_add_reg_contract_1_post =
 (bir_add_reg_I)
`;


(* contract two: loop body *)
(* from cjmp to cjmp *)
val bir_add_reg_contract_2_pre_def = Define `bir_add_reg_contract_2_pre =
^(band(``bir_add_reg_I``, bir_add_reg_loop_condition))
`;
val bir_add_reg_contract_2_post_def = Define `bir_add_reg_contract_2_post =
 bir_add_reg_I
`;

(* contract three: loop exit *)
(* from cjmp to end of function except ret and sp operations *)
val bir_add_reg_contract_3_pre_def = Define `bir_add_reg_contract_3_pre =
^(band(``bir_add_reg_I``, bnot bir_add_reg_loop_condition))
`;
val bir_add_reg_contract_3_post_def = Define `bir_add_reg_contract_3_post =
 bir_add_reg_post
`;








val y_addr = ``0w:word64``;
val x_addr = ``8w:word64``;
val ly_addr = ``16w:word64``;
val lx_addr = ``24w:word64``;
val y_var = ``(arm8_load_64 m.MEM (m.SP_EL0+(^y_addr)))``;
val x_var = ``(arm8_load_64 m.MEM (m.SP_EL0+(^x_addr)))``;
val ly_var = ``(arm8_load_64 m.MEM (m.SP_EL0+(^ly_addr)))``;
val lx_var = ``(arm8_load_64 m.MEM (m.SP_EL0+(^lx_addr)))``;

val arm8_sp_ok = ``(m.SP_EL0 >=+ 0xC0000000w) /\ (m.SP_EL0 <+ 0xD0000000w)``;




val arm8_add_pre_def = Define `arm8_add_pre m =
  ((^x_var) >= 0w) /\
  (^arm8_sp_ok)
`;
val arm8_add_post_def = Define `arm8_add_post m =
  ((^x_var+^y_var) = (^ly_var)) /\
  (^arm8_sp_ok)
`;

val get_y = ``(BExp_Load
       (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                              (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                              (BExp_Const (Imm64 (^y_addr)))) BEnd_LittleEndian
                        Bit64)``;
val get_x = ``(BExp_Load
       (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                              (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                              (BExp_Const (Imm64 (^x_addr)))) BEnd_LittleEndian
                        Bit64)``;
val get_ly = ``(BExp_Load
       (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                              (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                              (BExp_Const (Imm64 (^ly_addr)))) BEnd_LittleEndian
                        Bit64)``;
val get_lx = ``(BExp_Load
       (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                              (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                              (BExp_Const (Imm64 (^lx_addr)))) BEnd_LittleEndian
                        Bit64)``;


val bir_sp_ok = 
band (
     bnot (blt((bden (bvar "SP_EL0" ``(BType_Imm Bit64)``)),(bconst64 0xC0000000))),
     blt((bden (bvar "SP_EL0" ``(BType_Imm Bit64)``)),(bconst64 0xD0000000))
     );



val bir_add_pre_def = Define `bir_add_pre =
^(band
  (bnot (bslt(get_x, bconst64 0)),
   bir_sp_ok ))
`;

val bir_add_post_def = Define `bir_add_post =
^(bandl [
        (beq (bplus(get_y, get_x), get_ly)),
      bir_sp_ok
      ])`;


val original_loop_condition = (bnot (bsle(get_lx, bconst64 0)));
val bir_loop_condition =  bnot ``(BExp_BinExp BIExp_Or
                       (BExp_UnaryExp BIExp_Not
                          (BExp_BinPred BIExp_Equal
                             (BExp_Den (BVar "ProcState_N" BType_Bool))
                             (BExp_Den (BVar "ProcState_V" BType_Bool))))
                       (BExp_Den (BVar "ProcState_Z" BType_Bool)))``;


val bir_add_I_def = Define `bir_add_I =
^(bandl [
      (beq (bplus(get_y, get_x), bplus(get_ly, get_lx))),
   (beq (original_loop_condition, bir_loop_condition)),
   bir_sp_ok
   ])
`;


(* contract one *)
(* from function entry (we avoid stack pointer operations) to cjmp *)
val bir_contract_1_pre_def = Define `bir_contract_1_pre =
 (bir_add_pre)
`;
val bir_contract_1_post_def = Define `bir_contract_1_post =
 (bir_add_I)
`;


(* contract two: loop body *)
(* from cjmp to cjmp *)
val bir_contract_2_pre_def = Define `bir_contract_2_pre =
^(band(``bir_add_I``, bir_loop_condition))
`;
val bir_contract_2_post_def = Define `bir_contract_2_post =
 bir_add_I
`;

(* contract three: loop exit *)
(* from cjmp to end of function except ret and sp operations *)
val bir_contract_3_pre_def = Define `bir_contract_3_pre =
^(band(``bir_add_I``, bnot bir_loop_condition))
`;
val bir_contract_3_post_def = Define `bir_contract_3_post =
 bir_add_post
`;


(* old things *)




val bir_I_is_bool_pred_thm = prove(
  ``bir_is_bool_exp b_sqrt_I``,

FULL_SIMP_TAC (std_ss++bir_is_bool_ss) [b_sqrt_I_def]
);

val arm8I_imp_bI_thm = store_thm("arm8I_imp_bI_thm", 
``bir_pre_arm8_to_bir arm8_sqrt_I b_sqrt_I``
,
FULL_SIMP_TAC (std_ss) [bir_pre_arm8_to_bir_def, bir_I_is_bool_pred_thm] >>
REPEAT STRIP_TAC >>
SIMP_TAC (std_ss) [b_sqrt_I_def, bir_expTheory.bir_eval_exp_def] >>
(SIMP_TAC (std_ss) (((CONJUNCTS o UNDISCH o fst o EQ_IMP_RULE) bir_lifting_machinesTheory.arm8_bmr_rel_EVAL) @
  [bir_expTheory.bir_eval_bin_exp_REWRS, bir_immTheory.type_of_bir_imm_def,
         bir_exp_immTheory.bir_bin_exp_REWRS, bir_exp_immTheory.bir_bin_exp_GET_OPER_def] @
  [bir_expTheory.bir_eval_bin_pred_REWRS, bir_immTheory.type_of_bir_imm_def,
         bir_exp_immTheory.bir_bin_pred_REWRS, bir_exp_immTheory.bir_bin_pred_GET_OPER_def,
         bir_immTheory.bool2b_def] @
  [(UNDISCH o (SPECL [``bs:bir_state_t``, ``ms:arm8_state``])) bload_64_to_arm8_load_64_thm] @
  [bir_bool_expTheory.BVal_Imm_bool2b_EQ_TF_REWRS, bir_valuesTheory.BType_Bool_def ])) >>
FULL_SIMP_TAC (std_ss) [arm8_sqrt_I_def] >>
FULL_SIMP_TAC (std_ss) [bool2w_def, bir_bool_expTheory.bir_val_true_def] >>
EVAL_TAC
);


val bI_imp_arm8I_thm = store_thm("bI_imp_arm8I_thm",
``
bir_post_bir_to_arm8  arm8_sqrt_I b_sqrt_I 
``,
FULL_SIMP_TAC (std_ss) [bir_post_bir_to_arm8_def] >>
REPEAT STRIP_TAC >>
FULL_SIMP_TAC (std_ss) [b_sqrt_I_def, bir_expTheory.bir_eval_exp_def] >>
(FULL_SIMP_TAC (std_ss) (((CONJUNCTS o UNDISCH o fst o EQ_IMP_RULE) bir_lifting_machinesTheory.arm8_bmr_rel_EVAL) @
  [bir_expTheory.bir_eval_bin_exp_REWRS, bir_immTheory.type_of_bir_imm_def,
         bir_exp_immTheory.bir_bin_exp_REWRS, bir_exp_immTheory.bir_bin_exp_GET_OPER_def] @
  [bir_expTheory.bir_eval_bin_pred_REWRS, bir_immTheory.type_of_bir_imm_def,
         bir_exp_immTheory.bir_bin_pred_REWRS, bir_exp_immTheory.bir_bin_pred_GET_OPER_def,
         bir_immTheory.bool2b_def] @
  [(UNDISCH o (SPECL [``bs:bir_state_t``, ``ms:arm8_state``])) bload_64_to_arm8_load_64_thm] @
  [bir_bool_expTheory.BVal_Imm_bool2b_EQ_TF_REWRS, bir_valuesTheory.BType_Bool_def ])) >>
FULL_SIMP_TAC (std_ss) [arm8_sqrt_I_def] >>
FULL_SIMP_TAC (std_ss) [bir_immTheory.bool2w_11, bool2w_and, bir_bool_expTheory.bir_val_true_def, imm_eq_to_val_eq, bir_bool_expTheory.bool2w_ELIMS] 
);









(*
open bir_subprogramLib;
open bir_programSyntax;

val (_, bir_prog) =
         dest_comb
           (concl examples_arm8_program_THM);

val tutorial_prog_def = Define `tutorial_prog = ^bir_prog`;

EVAL ``MEM (BL_Address (Imm64 0x70cw)) (bir_labels_of_program tutorial_prog)``;
EVAL ``arm8_wf_varset (bir_vars_of_exp b_sqrt_I)``;
EVAL ``(bir_vars_of_exp b_sqrt_I)``;
EVAL ``(bir_vars_of_program tutorial_prog)``;
*)

val _ = export_theory();
