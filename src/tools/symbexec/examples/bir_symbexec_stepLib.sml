structure bir_symbexec_stepLib =
struct

local
  open bir_symbexec_stateLib;
  open bir_symbexec_coreLib;
in (* outermost local *)

(* execution of a basic statement *)
local
  (* basic statement execution functions *)
  (*
  val syst = init_state prog_vars;
  val SymbState systr = syst;
  val s = ``BStmt_Assign (BVar "R5" (BType_Imm Bit32)) (BExp_Den (BVar "R4" (BType_Imm Bit32)))``;
  val (bv, be) = dest_BStmt_Assign s
  *)
  fun state_exec_assign (bv, be) syst =
    if bir_expSyntax.is_BExp_IfThenElse be then
      let
        val (cnd, be1, be2) = bir_expSyntax.dest_BExp_IfThenElse be;
      in
        state_branch "assign"
                     cnd
                     (state_exec_assign (bv, be1))
                     (state_exec_assign (bv, be2))
                     syst
      end
    else
      state_assign_bv bv be syst;

  fun state_exec_assert cnd syst =
        state_branch_simp
           "assert"
           cnd
           (I)
           (SYST_update_status BST_AssertionViolated_tm)
           syst;

  fun state_exec_assume cnd syst =
        state_branch_simp
           "assume"
           cnd
           (I)
           (SYST_update_status BST_AssumptionViolated_tm)
           syst;

  fun state_exec_observe (id_tm, cnd_tm, exps_tm, ofun_tm) syst =
    let
      val _  = if numSyntax.is_numeral id_tm then () else
               raise ERR "symb_exec_stmt_observe" "the observation id has to be a numeral.";
      val id = numSyntax.dest_numeral id_tm;

      val (exp_tms,_) = listSyntax.dest_list exps_tm;

      val cnd_bv = bir_envSyntax.mk_BVar_string ("observe_cnd", ``BType_Bool``);

      fun fold_exp (exp_tm, (exp_bvs, insert_fun)) =
        let
          (* TODO: fix this, it needs to use type checking to be of the right type *)
          val exp_ty = ``BType_Bool``;
          val exp_bv = bir_envSyntax.mk_BVar_string ("observe_exp", exp_ty);
        in
          (exp_bv::exp_bvs, (state_insert_symbval_from_be exp_bv exp_tm) o insert_fun)
        end;
      val (exp_bvs, insert_fun) = List.foldr fold_exp ([],I) exp_tms; 

      val obs = (id, cnd_bv, exp_bvs, ofun_tm);
      val obss' = obs::(SYST_get_obss syst);
    in
      [(SYST_update_obss obss' o
        insert_fun o
        state_insert_symbval_from_be cnd_bv cnd_tm
        ) syst]
    end;

  open bir_programSyntax;
in (* local *)
  fun symb_exec_stmt (s, syst) =
    (* no update if state is not running *)
    if SYST_get_status syst <> BST_Running_tm then
      [syst]
    (* assignment *)
    else if is_BStmt_Assign s then
      state_exec_assign (dest_BStmt_Assign s) syst
    (* assert and assume *)
    else if is_BStmt_Assert s then
      state_exec_assert (dest_BStmt_Assert s) syst
    else if is_BStmt_Assume s then
      state_exec_assume (dest_BStmt_Assume s) syst
    (* observations *)
    else if is_BStmt_Observe s then
      state_exec_observe (dest_BStmt_Observe s) syst
    else raise ERR "symb_exec_stmt" ("unknown statement type for: " ^ (term_to_string s));
end (* local *)

(* execution of an end statement *)
local
  fun state_exec_try_jmp_label est syst =
    SOME (
    let
      val (vs, _) = hol88Lib.match ``BStmt_Jmp (BLE_Label xyz)`` est;
      val tgt     = (fst o hd) vs;
    in
      [SYST_update_pc tgt syst]
    end
    )
    handle HOL_ERR _ => NONE;

  fun state_exec_try_cjmp_label est syst =
    SOME (
    let
      val (vs, _) = hol88Lib.match ``BStmt_CJmp xyzc (BLE_Label xyz1) (BLE_Label xyz2)`` est;
      val cnd     = fst (List.nth (vs, 0));
      val tgt1    = fst (List.nth (vs, 1));
      val tgt2    = fst (List.nth (vs, 2));

      (* see whether the latest addition to the path condition
         matches the unnegated or negated branch condition *)
      val pred = SYST_get_pred syst;
      val vals = SYST_get_vals syst;
      val last_pred_bv = hd pred
                      handle Empty => raise ERR "symb_exec_endstmt" "oh no, pred is empty!";
      val last_pred_symbv = find_bv_val "symb_exec_endstmt" vals last_pred_bv;
      val last_pred_exp =
         case last_pred_symbv of
            SymbValBE (x,_) => x
          | _ => raise ERR "symb_exec_endstmt" "cannot handle symbolic value type for last pred exp";

      (* get branch condition *)
      val cnd_exp =
         case compute_valbe cnd syst of
            SymbValBE (x,_) => x
          | _ => raise ERR "symb_exec_endstmt" "cannot handle symbolic value type for conditions";
    in
      (* does unnegated condition match? *)
      if cnd_exp = last_pred_exp then
        [(SYST_update_pc tgt1
         ) syst]
      (* does negated condition match? *)
      else if bslSyntax.bnot cnd_exp = last_pred_exp then
        [(SYST_update_pc tgt2
         ) syst]
      (* no match *)
      else
      state_branch_simp
         "cjmp"
         cnd
         (SYST_update_pc tgt1)
         (SYST_update_pc tgt2)
         syst
    end
    )
    handle HOL_ERR _ => NONE;

  open bir_cfgLib;

  fun state_exec_from_cfg n_dict lbl_tm syst =
    let
      val n:cfg_node = binariesCfgLib.find_node n_dict lbl_tm;
      val n_type  = #CFGN_type n;
      val _       = if cfg_nodetype_is_call n_type orelse n_type = CFGNT_Jump then () else
                    raise ERR "symb_exec_endstmt" ("unexpected 2 at " ^ (term_to_string lbl_tm));
      val n_targets  = #CFGN_targets n;
      val lbl_tms = n_targets
    in
      List.map (fn t => SYST_update_pc t syst) lbl_tms
    end;

in (* local *)
  fun symb_exec_endstmt n_dict lbl_tm est syst =
    (* no update if state is not running *)
    if SYST_get_status syst <> BST_Running_tm then [syst] else
    (* try to match direct jump *)
    case state_exec_try_jmp_label est syst of
       SOME systs => systs
     | NONE       => (
    (* try to match direct branch *)
    case state_exec_try_cjmp_label est syst of
       SOME systs => systs
     | NONE       => (
    (* no match, then we have some indirection and need to use cfg (or it's another end statement) *)
    state_exec_from_cfg n_dict lbl_tm syst
    ));
end (* local *)


local
  open bir_block_collectionLib;
in (* local *)
  (* execution of a whole block *)
  fun symb_exec_block cfb n_dict bl_dict syst =
    let
      val lbl_tm = SYST_get_pc syst;

      val bl = (valOf o (lookup_block_dict bl_dict)) lbl_tm;
      val (_, stmts, est) = dest_bir_block bl;
      val s_tms = (fst o listSyntax.dest_list) stmts;

      val systs2 = List.foldl (fn (s, systs) => List.concat(List.map (fn x => symb_exec_stmt (s,x)) systs)) [syst] s_tms;

      (* generate list of states from end statement *)
      val systs = List.concat(List.map (symb_exec_endstmt n_dict lbl_tm est) systs2);
      val systs_filtered = if cfb andalso length systs > 1 then
                             List.filter check_feasible systs
                           else
                             systs;
    in
      systs_filtered
    end;

  (* execution of blocks until not running anymore or end label set is reached *)
  fun symb_exec_to_stop cfb _      _       []                  _            acc = acc
    | symb_exec_to_stop cfb n_dict bl_dict (exec_st::exec_sts) stop_lbl_tms acc =
        let
          fun state_stops syst =
            (List.exists (fn x => (SYST_get_pc syst) = x) stop_lbl_tms) orelse
            SYST_get_status syst <> BST_Running_tm;

          val sts = symb_exec_block cfb n_dict bl_dict exec_st;
          val (new_acc, new_exec_sts) = List.partition state_stops sts;
        in
          symb_exec_to_stop cfb n_dict bl_dict (new_exec_sts@exec_sts) stop_lbl_tms (new_acc@acc)
        end;
end (* local *)

end (* outermost local *)

end (* struct *)
