open HolKernel boolLib liteLib simpLib Parse bossLib;
open bir_inst_liftingTheory
open bir_lifting_machinesTheory
open bir_lifting_machinesLib;
open bir_interval_expTheory bir_update_blockTheory
open bir_exp_liftingLib bir_typing_expSyntax
open bir_typing_expTheory
open bir_programSyntax bir_interval_expSyntax


(**********)
(* Syntax *)
(**********)

val ERR = mk_HOL_ERR "bir_inst_liftingLib"
fun failwith s = raise (ERR "???" s)

fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "bir_inst_lifting"

val syntax_fns1 = syntax_fns 1 HolKernel.dest_monop HolKernel.mk_monop;
val syntax_fns3 = syntax_fns 3 HolKernel.dest_triop HolKernel.mk_triop;

fun get_const name = prim_mk_const{Name=name,        Thy="bir_inst_lifting"}

val bir_assert_desc_t_ty =
   Type.mk_thy_type {Tyop = "bir_assert_desc_t", Thy = "bir_update_block", Args = []};


val bir_updateE_desc_exp_tm = prim_mk_const{Name="bir_updateE_desc_exp", Thy="bir_update_block"}

val block_observe_ty = mk_vartype ":'observation_type"

val bir_is_lifted_inst_block_COMPUTE_block_tm =
   inst [Type.alpha |-> block_observe_ty] (get_const "bir_is_lifted_inst_block_COMPUTE_block")

val bmr_ms_mem_contains_tm = get_const "bmr_ms_mem_contains";

val bir_is_lifted_inst_block_COMPUTE_precond_tm =
    inst [Type.delta |-> block_observe_ty] (get_const "bir_is_lifted_inst_block_COMPUTE_precond")

val bir_is_lifted_inst_block_COMPUTE_ms'_COND_WITH_DESC_OK_tm =
  get_const "bir_is_lifted_inst_block_COMPUTE_ms'_COND_WITH_DESC_OK";

val bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_NO_UPDATES_tm =
  get_const "bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_NO_UPDATES";

val bir_is_lifted_inst_block_COMPUTE_mem_COND_NO_UPDATES_tm =
  get_const "bir_is_lifted_inst_block_COMPUTE_mem_COND_NO_UPDATES";


(******************)
(* Auxilary stuff *)
(******************)

(* If lifting of an instruction fails, it is returned (hexcode) together with
   some explantion in the from of a bir_inst_liftingExn_data value. *)

datatype bir_inst_liftingExn_data =
   BILED_msg of string
 | BILED_msg_term of string * term
 | BILED_lifting_failed of term
exception bir_inst_liftingExn of string * bir_inst_liftingExn_data;

exception bir_inst_liftingAuxExn of bir_inst_liftingExn_data;



(****************)
(* Main functor *)
(****************)

functor bir_inst_liftingFunctor (MD : sig val mr : bmr_rec end) : bir_inst_lifting = struct
  (* For debugging
  structure MD = struct val mr = arm8_bmr_rec end;
  val pc = Arbnum.fromInt 0x10000
  val (_, mu_thm) = mk_WI_end_of_nums_WFE ``:64`` (Arbnum.fromInt 0x1000) (Arbnum.fromInt 0x100000)

  fun hex_code_of_asm asm = hd (arm8AssemblerLib.arm8_code asm)


  val hex_code = hex_code_of_asm `adds x0, x1, #1`
  val hex_code = hex_code_of_asm `add x0, x1, x2`
  val hex_code = hex_code_of_asm `ldr x0, [x1, #8]`
  val hex_code = hex_code_of_asm `cmp x0, #0`
  val hex_code = hex_code_of_asm `lsl x0, x2, #8`
  val hex_code = hex_code_of_asm `add w0, w1, w2`
  val hex_code = hex_code_of_asm `adds w0, w1, w2`
  val hex_code = hex_code_of_asm `MOV x0 , x1`
  val hex_code = hex_code_of_asm `ADD X0, X1, W2, SXTW`
  val hex_code = hex_code_of_asm `LDRSW X0, [X1, #8]`
  val hex_code = hex_code_of_asm `lsl x0, x2, #8`
  val hex_code = hex_code_of_asm `ldr x0, [x2, #0]`
  val hex_code = hex_code_of_asm `adds x1, x1, #0`

  val hex_code = "D65F03C0";
  val hex_code = "12001C00"
*)

  open MD;

  (*****************)
  (* Preprocessing *)
  (*****************)

  (* The following code looks at the parameter of the functor and
     precomputes certain values that are needed later a lot. *)

  (* destruct the record to get the components easily *)
  val (mr_imms, mr_mem, mr_pc, _, mr_step_rel) = bmr_rec_extract_fields mr

  (* Some useful vars of the right type *)
  val (ms_ty, addr_sz_ty, mem_val_sz_ty)  = dest_bir_lifting_machine_rec_t_ty (type_of (#bmr_const mr))
  val ms_v = mk_var ("ms", ms_ty);
  val bs_v = mk_var ("bs", bir_state_t_ty);

  val bmr_eval_REWRS = let
    val tms = [
       (mk_icomb (bmr_mem_lf_tm, (#bmr_const mr))),
       (mk_icomb (bmr_pc_lf_tm, (#bmr_const mr))),
       (mk_icomb (bmr_pc_var_tm, (#bmr_const mr))),
       (mk_icomb (bmr_pc_var_cond_tm, (#bmr_const mr))),
       (mk_icomb (bmr_mem_var_tm, (#bmr_const mr))),
       (mk_icomb (bmr_field_step_fun_tm, (#bmr_const mr))),
       (mk_icomb (bmr_field_extra_tm, (#bmr_const mr))),
       (mk_bmr_field_imms (#bmr_const mr)),
       (mk_bmr_field_pc (#bmr_const mr)),
       (mk_bmr_field_mem (#bmr_const mr))]
    val thms0 = map (SIMP_CONV (std_ss++bmr_ss) [(#bmr_eval_thm mr),
       bmr_mem_lf_def, bmr_pc_lf_def, bmr_pc_var_cond_def, bmr_pc_var_def,
       bmr_mem_var_def]) tms
    val thms1 = map GEN_ALL thms0
  in
    LIST_CONJ thms1
  end;


  fun mk_mem_addr_from_num (n:num) =
    wordsSyntax.mk_n2w (numSyntax.mk_numeral n, addr_sz_ty);

  (* Insiantiate some useful syntax funs *)
  val (pc_sz, mk_pc_of_term) = bmr_rec_mk_pc_of_term mr
  val mk_label_of_num = bmr_rec_mk_label_of_num mr
  val mk_label_of_num_eq_pc = bmr_rec_mk_label_of_num_eq_pc mr;


  (* Instantiate the inst_lifting theorem with the record and types. *)
  val inst_lift_THM = let
     val thm0 = INST_TYPE [mk_vartype "'o" |-> block_observe_ty]
           (bir_is_lifted_inst_block_COMPUTE_OPTIMISED);
     val thm1 = ISPEC (#bmr_const mr) thm0;
     val thm2 = MP thm1 (#bmr_ok_thm mr)
  in thm2 end;

  val inst_lift_THM_ex_vars = let
    val (_, t)  = dest_forall (concl inst_lift_THM)
    val (_, t)  = dest_imp_only t
    val (_, t)  = strip_forall t
    val (_, t)  = dest_imp_only t
    val (_, t)  = strip_forall t
    val (t, _)  = dest_imp_only t
    val (_, t)  = strip_forall t
    val (vs, _) = strip_exists t
  in vs end;

  val bir_is_lifted_inst_block_COMPUTE_precond_tm_mr =
    list_mk_comb (
      mk_icomb ( bir_is_lifted_inst_block_COMPUTE_precond_tm, #bmr_const mr),
      [bs_v, ms_v]);

  val comp_thm_updates_FULL_INTRO =
    ISPECL [(#bmr_const mr), bs_v] bir_is_lifted_inst_block_COMPUTE_updates_FULL_INTRO;

  val comp_thm_updates_ADD_IMM_UP =
    ISPECL [(#bmr_const mr), bs_v] bir_is_lifted_inst_block_COMPUTE_updates_FULL_REL___ADD_IMM_UP;

  val comp_thm_updates_ADD_IMM_UP_NONE =
    ISPECL [(#bmr_const mr), bs_v] bir_is_lifted_inst_block_COMPUTE_updates_FULL_REL___ADD_IMM_UP_NONE;

  val comp_thm_updates_INTRO_MEM =
    ISPECL [(#bmr_const mr), bs_v] bir_is_lifted_inst_block_COMPUTE_updates_FULL_REL___INTRO_MEM;

  val comp_thm_updates_INTRO_NO_MEM =
    ISPECL [(#bmr_const mr), bs_v] bir_is_lifted_inst_block_COMPUTE_updates_FULL_REL___INTRO_NO_MEM;

  val comp_thm_eup_JMP = let
     val thm0 = ISPECL [#bmr_const mr, bs_v]
          bir_is_lifted_inst_block_COMPUTE_eup_COND_FIXED_VARS___JMP
  in thm0 end;

  val comp_thm_eup_CJMP = let
     val thm0 = ISPECL [#bmr_const mr, bs_v, ms_v]
          bir_is_lifted_inst_block_COMPUTE_eup_COND_FIXED_VARS___CJMP
     val thm1 = UNDISCH (MP thm0 (#bmr_ok_thm mr))
  in thm1 end;

  val comp_thm_eup_XJMP = let
     val thm0 = ISPECL [#bmr_const mr, bs_v, ms_v]
          bir_is_lifted_inst_block_COMPUTE_eup_COND_FIXED_VARS___XJMP
     val thm1 = UNDISCH (MP thm0 (#bmr_ok_thm mr))
  in thm1 end;


  (* Construct the extra thms *)
  val ms_extra_REWRS = let
     val thm0 = SPECL [bs_v, ms_v] (ISPEC (#bmr_const mr) bmr_rel_implies_extra)
     val thm1 = UNDISCH thm0
     val thm2 = SIMP_RULE (std_ss) [bmr_eval_REWRS] thm1
  in thm2 end;


  (* preinstantiated bmr_ms_mem_contains term *)
  val bmr_ms_mem_contains_tm_mr = let
    val tm1 = mk_icomb (bmr_ms_mem_contains_tm, (#bmr_const mr))
    val tm2 = mk_comb (tm1, ms_v)
  in tm2 end;


  (* precomputed imms_lifting *)
  val mr_imms_lf_of_ms = let
    fun do_it tm = let
      val (_, lf_tm) = dest_BMLI tm
      val tm0 = mk_comb (lf_tm, ms_v)
      val tm1 = rhs (concl (SIMP_CONV std_ss [] tm0)) handle UNCHANGED => tm0
    in (tm, tm1) end
  in List.map do_it mr_imms end;

  (* precompute mem lifting *)
  val mr_mem_lf_of_ms = let
    val (_, lf_tm) = dest_BMLM mr_mem
    val tm0 = mk_comb (lf_tm, ms_v)
    val tm1 = rhs (concl (SIMP_CONV std_ss [] tm0)) handle UNCHANGED => tm0
  in tm1 end;

  (* precompute pc lifting *)
  val (pc_var_t, pc_cond_var_t, mr_pc_lf_of_ms) = let
    val (pc_var_t, pc_cond_var_t, lf_tm) = dest_BMLPC mr_pc
    val tm0 = mk_comb (lf_tm, ms_v)
    val tm1 = rhs (concl (SIMP_CONV std_ss [] tm0)) handle UNCHANGED => tm0
  in (pc_var_t, pc_cond_var_t, tm1) end;


  (* Constructing net for expression lifting. The _raw version does the lifting for
     the environment in a specially prepared net. Since we usually want the whole
     lifting to fail, if some preconds remain, the wrapper exp_lift_fn checks for
     the existence of such preconds. Notice that this does not mean hypothesis, i.e.
     according to the implementation of bir_exp_lift only "bir_is_lifted_exp" terms. *)
  val exp_lift_fn_raw = let
     val eln0 = eln_default
     val eln1 = eln_add_thms eln0 [bs_v, ms_v] [SPECL [bs_v, ms_v] (#bmr_lifted_thm mr)]
     val eln2 = eln_add_thms eln1 [] (#bmr_extra_lifted_thms mr)
     val env_t = mk_bst_environ bs_v
  in
     bir_exp_lift env_t eln2
  end;

  fun exp_lift_fn tm = let
     val res = exp_lift_fn_raw tm
     val _ = if is_imp_only (concl res) then failwith "exp_lift_fn: preconds present" else ()
  in
     res
  end handle HOL_ERR _ =>
    raise (bir_inst_liftingAuxExn (BILED_lifting_failed tm));


  (*******************************************************)
  (* Creating lifting theorems from a single instruction *)
  (*******************************************************)

  (* Given the hex-code of an instruction and a PC in form of a number
     to load it from, the first step is to create corresponding step theorems.

     These step theorems are instantiated with the concrete value of the PC,
     as many as possible preconditions are removed using the fact that the machine
     state is satisfying the extra predicate.

     In the remaining conditions, a memory region is searched that contains that
     instruction and these preconditions are transformed into the
     bmr_ms_mem_contains form.

     The list of resulting theorems, the computed memory mapping and the
     label corresponding to the given PC are returned. *)

  fun mk_inst_lifting_theorems (pc : Arbnum.num) hex_code =
  let
     val lifted_thms_raw = let
       val res = (#bmr_step_hex mr) ms_v hex_code
       val _ = assert (not o List.null) res
     in res end handle HOL_ERR _ =>
       raise (bir_inst_liftingExn (hex_code, BILED_msg "bmr_step_hex failed"));

     (* instantiate pc and compute label *)
     val (label_tm, pc_thm) = let
        val thm0 = SPECL [ms_v, numSyntax.mk_numeral pc] (#bmr_label_thm mr);
        val tm = rhs (#1 (dest_imp_only (concl thm0)))
     in (tm, UNDISCH thm0) end handle HOL_ERR _ =>
       raise (bir_inst_liftingExn (hex_code, BILED_msg "label thm failed"));

     (* Normalise all resulting theorems *)
     fun norm_thm thm =
        SIMP_RULE std_ss [pc_thm, ms_extra_REWRS, satTheory.AND_IMP,
           alignmentTheory.aligned_numeric, wordsTheory.word_add_n2w] thm handle UNCHANGED => thm
     fun inst_extra_vars thm = let
        val (preconds, _) = strip_imp_only (concl thm)
        fun mk_var_subst (tm, s) = let
           val (v1, v2) = dest_eq (subst s tm)
        in
           (if (is_var v2) then (v2 |-> v1)::s else
            if (is_var v1) then (v1 |-> v2)::s else
            fail ())
        end handle HOL_ERR _ => s;
        val s = List.rev (foldl mk_var_subst [] preconds)
     in if (null s) then thm else
        REWRITE_RULE [] (INST s thm)
     end;
     val lifted_thms = map (inst_extra_vars o norm_thm) lifted_thms_raw;

     (* try to compute bmr_ms_mem_contains *)
     val (mm_tm, mm_thm) = let
       (* first get the common preconds *)
       val common_preconds = let
          fun preconds_of_thm thm =
            HOLset.addList (empty_tmset, fst (strip_imp_only (concl thm)))

          val preconds = foldl (fn (thm, s) => HOLset.intersection (s, preconds_of_thm thm))
             (preconds_of_thm (hd lifted_thms)) (tl lifted_thms)
          in HOLset.listItems preconds end

       (* the extract pairs of mem address and values *)
       val mem_precond_pairs = Lib.mapfilter (fn tm => let
          val (l_tm, v_tm) = dest_eq tm;
          val (ms_t, a_tm) = (#bmr_dest_mem mr) l_tm
          val _ = assert (aconv ms_v) ms_t
          val a_n = numSyntax.dest_numeral (fst (wordsSyntax.dest_n2w a_tm))
       in (a_n, v_tm, tm) end) common_preconds
       val _ = assert (not o List.null) mem_precond_pairs

       (* sort it and try to combine *)
       val sorted_mem_pairs = sort (fn (n1, _) => (fn (n2, _) => (Arbnum.< (n2, n1))))
          (map (fn (a, v, _) => (a,v)) mem_precond_pairs)
       val (n, vs) = foldl (fn ((n', v), (n, vs)) =>
         if (Arbnum.plus1 n' = n) then (n', v::vs) else fail())
         ((fn (n, v) => (n, [v])) (hd sorted_mem_pairs)) (tl sorted_mem_pairs)

       (* make the term *)
       val mm_tm = let
          val addr_tm =  mk_mem_addr_from_num n;
          val v_tm = listSyntax.mk_list (vs, type_of (hd vs))
       in pairSyntax.mk_pair (addr_tm, v_tm) end;

       (* show that this really implies all the preconds *)
       val precond_thm = let
         val p_tm = mk_comb (bmr_ms_mem_contains_tm_mr, mm_tm)
         val c_tm = list_mk_conj (map (fn (_, _, tm) => tm) mem_precond_pairs)
         val thm0 = prove (mk_imp (p_tm, c_tm),
             SIMP_TAC (std_ss++bmr_ss++wordsLib.WORD_ARITH_ss) [
                bmr_ms_mem_contains_def, bmr_mem_lf_def,
                (#bmr_eval_thm mr)]);
       in UNDISCH thm0 end;
     in (mm_tm, precond_thm) end handle HOL_ERR _ =>
       raise (bir_inst_liftingExn (hex_code, BILED_msg "mem region computation failed"));


     (* Rewrite with these new mm theorems *)
     val lifted_thms2 = map (REWRITE_RULE [mm_thm]) lifted_thms
  in
     (lifted_thms2, mm_tm, label_tm)
  end handle HOL_ERR _ =>
    raise (bir_inst_liftingExn (hex_code, BILED_msg "mk_inst_lifting_theorems failed"));


  (******************************)
  (* Preprocessing next-theorem *)
  (******************************)

  (* If multiple theorems are produced by the step function, we might want to
     preprocess them. If there are exactly 2, one might want to merge them for example.
     Each theorem is accompanied by condition. The code generated around the theorems
     has to guarantee, that this condition is satisfied, once the block belonging to
     this theorem is executed. *)

  fun preprocess_next_thms (lb:term) (pc:Arbnum.num) ([]:thm list) =
      failwith "preprocess_next_thms called with empty list"
    | preprocess_next_thms lb pc [thm] = [(lb, T, thm)]
    | preprocess_next_thms lb pc thms = failwith "TODO: implement this"



  (***********************************************)
  (* Lifting a single thm                        *)
  (***********************************************)

  (*----------------------*)
  (* Compute ms', al_step *)
  (*----------------------*)

  (* given a step theorem, compute the necessary preconditions and
     and lift them. This gives rise to al_step. Also extract the term ms'. *)

  fun compute_al_step_ms' next_thm0 =
  let
    (* all possible simplifications of remaining conditions have been tried before,
       so let's just lift everything *)
    val (preconds, next_tm) = strip_imp_only (concl next_thm0)
    val ms'_t = rand (rhs (next_tm))

    (* lift all preconds *)
    val lift_thms = map exp_lift_fn_raw preconds
    val assert_ok_thms = map (MATCH_MP bir_assert_desc_OK_via_lifting) lift_thms
    val al_step_l = map (fn thm => (rand (concl thm))) assert_ok_thms
    val al_step = listSyntax.mk_list (al_step_l, bir_assert_desc_t_ty)

    (* Show that computed ms' and al_step really are ok *)
    val thm_tm = let
       val t0 = mk_icomb (bir_is_lifted_inst_block_COMPUTE_ms'_COND_WITH_DESC_OK_tm,
          (#bmr_const mr))
       val t1 = list_mk_comb (t0, [bs_v, ms_v, al_step, ms'_t])

       val thm0 = SIMP_CONV (list_ss++(#bmr_extra_ss mr)) (assert_ok_thms@[
          next_thm0, ms_extra_REWRS,
          bir_is_lifted_inst_block_COMPUTE_ms'_COND_WITH_DESC_OK_def,
          bir_is_lifted_inst_block_COMPUTE_ms'_COND_def,
          bir_assert_desc_value_def,
          bmr_eval_REWRS]) t1
       val thm1 = EQT_ELIM thm0
    in thm1 end
  in
    (ms'_t, al_step, thm_tm)
  end;

  (*-----------------*)
  (* Compute imm_ups *)
  (*-----------------*)

  (* Given the new machine state as a term, figure out, which changes actually did
     happen. These are represented by the imm_ups list. We need this list as a term
     for later instantiating as well as only the changes as an SML datastructure for
     computing the block-updates later. Moreover, a theorem stating that the
     computed imm_ups list is correct is produced. *)

  fun compute_imm_ups ms'_t =
  let
    val compute_single_up_single_conv = SIMP_CONV (std_ss++(#bmr_extra_ss mr)++wordsLib.SIZES_ss) [
         updateTheory.APPLY_UPDATE_THM, wordsTheory.n2w_11]
    fun compute_single_up lf_ms = let
      val lf_ms'_tm = subst [ms_v |-> ms'_t] lf_ms
      val lf_ms'_thm = compute_single_up_single_conv lf_ms'_tm handle UNCHANGED => REFL lf_ms'_tm

      val res = rhs (concl lf_ms'_thm)
      val (upd_tm, upd_tm_opt) = if (aconv res lf_ms) then (optionSyntax.mk_none (type_of res), NONE) else
                      (optionSyntax.mk_some res, SOME res)
    in
      (upd_tm, upd_tm_opt, lf_ms'_thm)
    end;

    val (upds_tms, eval_thms) =
       foldl (fn ((bmli_tm, lf_ms), (resl, thmL)) =>
         let val (upd_tm, upd_opt, lf_ms'_thm) = compute_single_up lf_ms
             val resl' = pairSyntax.mk_pair (bmli_tm, upd_tm)::resl;
             val thml' = lf_ms'_thm :: thmL;
         in (resl', thml') end)
         ([], []) mr_imms_lf_of_ms

    val imm_ups_tm = listSyntax.mk_list (List.rev upds_tms, type_of (hd upds_tms))

    (* Show that computed imm_ups  is really are ok *)
    val thm_tm = let
       val t0 = mk_icomb (bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_NO_UPDATES_tm,
          (#bmr_const mr))
       val t1 = list_mk_comb (t0, [ms_v, ms'_t, imm_ups_tm])

       val thm1 = SIMP_CONV (std_ss) (eval_thms @ [
         bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_NO_UPDATES_EVAL, bmr_eval_REWRS,
         bir_is_lifted_inst_block_COMPUTE_imm_ups_COND_NO_UPDATES_CHECK_def])
         t1
       val thm2 = EQT_ELIM thm1
    in thm2 end
  in
    (imm_ups_tm, thm_tm)
  end;


  (*-----------------*)
  (* Compute mem_up *)
  (*-----------------*)

  (* Given a new state, we compute whether updates to the memory happend. This
     is similar to computing updates to immediates via compute_imm_ups.
     The computed term, its SML representation and a correctness theorem are returned. *)

  fun compute_mem_up ms'_t =
  let
     val lf_ms'_tm = subst [ms_v |-> ms'_t] mr_mem_lf_of_ms
     val lf_ms'_thm = SIMP_CONV (std_ss++(#bmr_extra_ss mr)++wordsLib.SIZES_ss) []
         lf_ms'_tm handle UNCHANGED => REFL lf_ms'_tm

      val res = rhs (concl lf_ms'_thm)

      val (upd_tm, upd_tm_opt) = if (aconv res mr_mem_lf_of_ms) then (optionSyntax.mk_none (type_of res), NONE) else
                      (optionSyntax.mk_some res, SOME res)

      (* !!!! TODO: support memory changes *)
      val _ = if upd_tm_opt <> NONE then fail () else ()

    (* Show that computed imm_ups  is really are ok *)
    val thm_tm = let
       val t0 = mk_icomb (bir_is_lifted_inst_block_COMPUTE_mem_COND_NO_UPDATES_tm,
          (#bmr_const mr))
       val t1 = list_mk_comb (t0, [ms_v, ms'_t, upd_tm])

       val thm0 = SIMP_CONV std_ss ([lf_ms'_thm, bmr_eval_REWRS,
           bir_is_lifted_inst_block_COMPUTE_mem_COND_NO_UPDATES_EVAL])
           t1
       val thm1 = EQT_ELIM thm0
    in thm1 end
  in
    (upd_tm, upd_tm_opt, thm_tm)
  end;


  (*-----------------*)
  (* Compute al_mem  *)
  (*-----------------*)

  (* Given

     - the next machine state ms'_t as a term
     - the region of memory that needs to remain unchanged in the form of a theorem
         mu_thm :   |- WI_wfe (WI_end _ _)
     - the memory in ms'_t if it changed compared to mem_ms'_t as a term option
     - and a theorem "mem_up_thm" stating that "mem_ms'_t_opt" is indeed sound. This
       is the theorem produced by compute_mem_up.

    we need to compute a list for assertions that enforce that the memory does not
    change in the region specified bz mu_thm.
    This list of assertions is returned together with a theorem stating its validity.

    If the memory is not updated, finding such a list is trival, just return the
    empty list of assertions.

    More interesting, if the memory is updated, we need to find out at which addressed.
    Usually this is a interval of addresses, seldomly multiple interval. The start of the
    interval usually depends on the current state, e.g. on the value stored in a register.
    So, we need an assertion to enforce that the addresses computed at runtime are not
    inside the protected region.
  *)

  (* Trivial case: nothing changed. Just use preproved theorem. *)
  fun compute_al_mem_NONE (ms'_t:term) (mu_thm:thm) mem_up_thm = let
    val al_mem_thm = let
      val thm0 = ISPEC (#bmr_const mr) (bir_is_lifted_inst_block_COMPUTE_al_mem_COND_WITH_DESC_OK_INTRO_NONE)
      val thm1 = SPECL [(rand (concl mu_thm)), bs_v, ms_v, ms'_t] thm0
      val thm2 = MP thm1 mem_up_thm
    in thm2 end;

    val al_mem_t = rand (concl al_mem_thm)
  in
    (al_mem_t, al_mem_thm)
  end;


  (* The interesting case where we actually need to do something *)
  fun compute_al_mem_SOME ms'_t mu_thm mem_ms'_t mem_up_thm = let
  in
     failwith ("TODO: implement it")
  end

  (* Combine both *)
  fun compute_al_mem ms'_t mu_thm real_mem_up_opt mem_up_thm = (
    case (real_mem_up_opt) of
        NONE => compute_al_mem_NONE ms'_t mu_thm mem_up_thm
      | SOME mem_ms' => compute_al_mem_SOME ms'_t mem_ms' mu_thm mem_up_thm
  );


  (*-------------*)
  (* Compute eup *)
  (*-------------*)

  (* Given a next state as a term, we look at the PC of the state and
     compute an end statement update description that allows us to jump to
     that PC. *)
  fun compute_eup ms'_t =
  let
     val lf_ms'_tm = list_mk_icomb bmr_pc_lf_tm [(#bmr_const mr), ms'_t];
     val lf_ms'_thm = SIMP_CONV (std_ss++(#bmr_extra_ss mr)++wordsLib.SIZES_ss) [bmr_eval_REWRS]
         lf_ms'_tm handle UNCHANGED => REFL lf_ms'_tm
     val res_imm = rhs (concl lf_ms'_thm)

     (* There are 3 cases supported:

        - simple unconditional jump : res is a literal word, e.g. 0x1000w
        - simple conditional jump : res is a conditional, with 2 literal words in the cases, e.g.
              if (some condition) then 0x1000w else 0x1008w
        - something fancy. res is an arbitrary, liftable word expression

        Just try them one after the other.
     *)

     fun compute_eup_JMP () = let
        (* Check we have a literal imm *)
        val (_, w) = bir_immSyntax.gen_dest_Imm res_imm
        val _ = if (wordsSyntax.is_word_literal w) then () else fail ()

        val thm0 = SPEC ms'_t comp_thm_eup_JMP
        val thm1 = PURE_REWRITE_RULE [lf_ms'_thm] thm0
     in
        thm1
     end;

     (* DEBUG
        val expand_thm = prove (``Imm64 w = Imm64 (if T then w else w)``, SIMP_TAC std_ss [])
        val lf_ms'_thm = ONCE_REWRITE_RULE [expand_thm] lf_ms'_thm
        val res_imm = rhs (concl lf_ms'_thm)
      *)
     fun compute_eup_CJMP () = let
        val (sz, i) = bir_immSyntax.gen_dest_Imm res_imm
        val (c, w1, w2) = boolSyntax.dest_cond i
        val _ = if (wordsSyntax.is_word_literal w1) then () else fail ()
        val _ = if (wordsSyntax.is_word_literal w2) then () else fail ()

        val lf_ms'_thm' = CONV_RULE (RHS_CONV (PURE_REWRITE_CONV [COND_RAND])) lf_ms'_thm
        val lift_thm = exp_lift_fn c

        val thm0 = SPECL [ms'_t, c, bir_immSyntax.gen_mk_Imm w1, bir_immSyntax.gen_mk_Imm w2] comp_thm_eup_CJMP
        val thm1 = REWRITE_RULE [lf_ms'_thm'] thm0
        val thm2 = MATCH_MP thm1 lift_thm
        val thm3 = PURE_REWRITE_RULE [bmr_eval_REWRS] thm2
     in
        thm3
     end;

     fun compute_eup_XJMP () = let
        val lift_thm = exp_lift_fn res_imm

        val thm0 = SPEC ms'_t comp_thm_eup_XJMP
        val thm1 = PURE_REWRITE_RULE [lf_ms'_thm] thm0
        val thm2 = MATCH_MP thm1 lift_thm
        val thm3 = PURE_REWRITE_RULE [bmr_eval_REWRS] thm2
     in
        thm3
     end;

     val eup_thm = compute_eup_JMP () handle HOL_ERR _ =>
                   compute_eup_CJMP () handle HOL_ERR _ =>
                   compute_eup_XJMP ();
     val eup_tm = rand (rator (concl eup_thm))
   in
     (eup_tm, eup_thm)
   end;


  (*-----------------*)
  (* Compute updates *)
  (*-----------------*)

  (* Given imm_ups, mem_up and the end description, the real updates,
     whether to use a temp var for the end description and theorem
     stating the correctness of the computed updates is derived.

     This mainly means lifting the values of imm_ups and mem_up and
     computing the flag whether to use temp vars by looking at which
     vars are still needed afterwards.
  *)
  local
     val vn_set_empty = HOLset.empty String.compare;

     (* compute var names of expression. Return both a theorem and add them to the given
        string set. *)
     val comp_varnames_conv = SIMP_CONV (std_ss++(#bmr_extra_ss mr)++pred_setSimps.PRED_SET_ss++HolBACoreSimps.holBACore_ss) [
         pred_setTheory.INSERT_UNION_EQ,
         bir_temp_varsTheory.bir_temp_var_name_def,
         bir_bool_expTheory.bir_exp_true_def,
         bir_bool_expTheory.bir_exp_false_def,
         bir_nzcv_expTheory.BExp_nzcv_ADD_vars_of, bir_nzcv_expTheory.BExp_nzcv_SUB_vars_of]

     val comp_upd_imm_varname_conv = SIMP_CONV (list_ss++stringSimps.STRING_ss) [bir_temp_varsTheory.bir_temp_var_def, bir_envTheory.bir_var_name_def, bir_temp_varsTheory.bir_temp_var_name_def]

     val comp_upd_imm_nin_conv = SIMP_CONV (list_ss++pred_setSimps.PRED_SET_ss++stringSimps.STRING_ss) []

     fun comp_varnames_thm e_tm = let
       val tm0 = pred_setSyntax.mk_image (bir_envSyntax.bir_var_name_tm,
                   (mk_bir_vars_of_exp e_tm))
       val thm0 = comp_varnames_conv tm0
     in
       thm0
     end handle UNCHANGED =>
        raise bir_inst_liftingAuxExn (BILED_msg_term ("failed to compute vars of exp", e_tm));

     fun comp_varnames e_tm vn_set = let
       val thm0 = comp_varnames_thm e_tm
       val vn_t = rhs (concl thm0)
       val vn_string_l = List.map stringSyntax.fromHOLstring (pred_setSyntax.strip_set vn_t)
       val vn_set' = HOLset.addList (vn_set, vn_string_l);
     in
       (thm0, vn_set')
     end;

     fun simplify_FULL_REL_vars_RULE thms =
       let
          val c = PURE_REWRITE_CONV (pred_setTheory.INSERT_UNION_EQ::pred_setTheory.UNION_EMPTY::thms)
       in
         CONV_RULE (RATOR_CONV (RATOR_CONV (RAND_CONV c)))
       end;

(*
     val vn_set0 = vn_set
     val full_rel_thm = init_thm

     val (full_rel_thm, vn_set) = foldl add_imm_up (init_thm, vn_set)
         (List.take (imm_ups_tm_list, 38));


     val (v_t, lf_t, SOME res_t) = el 39 imm_ups_tm_list
*)
     fun add_imm_up ((v_t, lf_t, NONE), (full_rel_thm, vn_set)) =
         (SPECL [v_t, lf_t] (MATCH_MP comp_thm_updates_ADD_IMM_UP_NONE full_rel_thm),
          vn_set)
       | add_imm_up ((v_t, lf_t, SOME res_t), (full_rel_thm, vn_set)) =
         let
           val lift_thm = PURE_REWRITE_RULE [bir_exp_liftingTheory.bir_is_lifted_exp_def]
              (exp_lift_fn res_t)
           val e_tm = rand (rator (concl lift_thm))

           val (vn_e_thm, vn_set') = comp_varnames e_tm vn_set

           (* compute temp *)
           val use_temp = let
             val vn_s = stringSyntax.fromHOLstring (fst(bir_envSyntax.dest_BVar v_t))
           in
             if HOLset.member (vn_set, vn_s) then T else F
           end;

           val thm0 = SPECL [v_t, lf_t, res_t, e_tm, use_temp] (MATCH_MP comp_thm_updates_ADD_IMM_UP full_rel_thm)
           val thm1 = MP thm0 lift_thm
           val (precond_tm, _) = dest_imp_only (concl thm1)

           val precond_thm = let
             val xthm0 = RAND_CONV (RATOR_CONV (RAND_CONV comp_upd_imm_varname_conv)) precond_tm
             val xthm1 = CONV_RULE (RHS_CONV comp_upd_imm_nin_conv) xthm0
             val xthm2 = EQT_ELIM xthm1
           in xthm2 end

           val thm3 = MP thm1 precond_thm
           val thm4 = simplify_FULL_REL_vars_RULE [vn_e_thm] thm3
         in
           (thm4, vn_set')
         end;

  in

  fun compute_updates mem_up_t imm_ups_t eup_t =
  let
     (* Deal with mem_up *)
     val (init_thm, vn_set) = if (optionSyntax.is_none mem_up_t) then
          (comp_thm_updates_INTRO_NO_MEM, vn_set_empty)
        else let
           (* DEBUG:
              val mem_up_t = optionSyntax.mk_some mr_mem_lf_of_ms
            *)
           val mem_ms' = optionSyntax.dest_some mem_up_t
           val lift_thm = exp_lift_fn mem_ms'
           val e_tm = rand (rator (concl lift_thm));
           val (e_thm, vn_set) = comp_varnames e_tm vn_set_empty

           val thm0 = SPECL [e_tm, mem_ms'] comp_thm_updates_INTRO_MEM
           val thm1 = MP thm0 lift_thm
           val thm2 = simplify_FULL_REL_vars_RULE [e_thm] thm1
        in
           (thm2, vn_set)
        end;

     (* Deal with imm_ups *)
     val imm_ups_tm_list = List.rev (
        List.map (fn t => let
           val (t1, res_opt_t) = pairSyntax.dest_pair t
           val res_opt = SOME (optionSyntax.dest_some res_opt_t) handle HOL_ERR _ => NONE;
           val (v_t, lf_t) = dest_BMLI t1
        in
           (v_t, lf_t, res_opt)
        end)
        (fst (listSyntax.dest_list imm_ups_t)));

     val (full_rel_thm, vn_set_final) = foldl add_imm_up (init_thm, vn_set)
         (List.take (imm_ups_tm_list, 38));

     val (full_rel_thm, vn_set_final) = foldl add_imm_up (init_thm, vn_set) imm_ups_tm_list;

     (* add eup *)
     val (eup_thm, eup_temp_tm) = let
       val thm0 = SPEC eup_t (MATCH_MP comp_thm_updates_FULL_INTRO full_rel_thm)

       val (eup_temp_v, precond_tm, updates_tm) = let
          val (eup_temp_v, t0) = dest_forall (concl thm0)
          val (precond_tm, t1) = dest_imp_only t0
          val updates_tm = rand t1
       in (eup_temp_v, precond_tm, updates_tm) end;
       val updates_thm = SIMP_CONV list_ss [bmr_eval_REWRS] updates_tm

       val e_thm = REWRITE_CONV [bir_updateE_desc_exp_def] (mk_comb (bir_updateE_desc_exp_tm, eup_t))
       val e_opt = SOME (optionSyntax.dest_some (rhs (concl e_thm))) handle HOL_ERR _ => NONE

       val (precond_thm, temp_t) = if (is_none e_opt) then
       let
         (* We don't have an exp, therefore the F case holds trivially *)
         val precond_thm = EQT_ELIM (REWRITE_CONV [e_thm, optionTheory.NOT_NONE_SOME] (subst [eup_temp_v |-> F] precond_tm))
       in
         (precond_thm, F)
       end else if (listSyntax.is_null (rhs (concl updates_thm))) then (
       let
         (* We don't have have any other changes, therefore the F case holds trivially *)
         val precond_thm = EQT_ELIM (
            REWRITE_CONV [updates_thm, bir_is_lifted_inst_block_COMPUTE_updates_UPDATES_VARS_REWRS,
              pred_setTheory.DISJOINT_EMPTY] (subst [eup_temp_v |-> F] precond_tm)
         )
       in
         (precond_thm, F)
       end) else (let
         (* We are in a more tricky situation. We just try it. *)
         val precond_thm0 = REWRITE_CONV [e_thm, updates_thm,
            bir_updateE_desc_var_def, optionTheory.option_CLAUSES] precond_tm
       in
         let
            val thm0 = INST [eup_temp_v |-> F] precond_thm0
            val vars_thm = comp_varnames_thm (valOf e_opt)
            val thm1 = CONV_RULE (RHS_CONV (SIMP_CONV (std_ss) [vars_thm,
              bir_is_lifted_inst_block_COMPUTE_updates_UPDATES_VARS_REWRS])) thm0
            val thm2 = CONV_RULE (RHS_CONV (SIMP_CONV (list_ss++stringSimps.STRING_ss) [
               pred_setTheory.DISJOINT_EMPTY, pred_setTheory.DISJOINT_INSERT])) thm1
         in (EQT_ELIM thm2, F) end handle HOL_ERR _ => let
            val thm0 = INST [eup_temp_v |-> T] precond_thm0
            val thm1 = CONV_RULE (RHS_CONV (SIMP_CONV (std_ss) [
               bir_envTheory.bir_var_name_def, pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY])) thm0
         in
            (EQT_ELIM thm1, T)
         end handle HOL_ERR _ => failwith "Could not prove precond"
       end);

       val thm1 = MP (SPEC temp_t thm0) precond_thm
       val thm2 = CONV_RULE (RAND_CONV (K updates_thm)) thm1
     in (thm2, temp_t) end;

     val updates_tm' = rand (concl eup_thm)
   in
     (updates_tm', eup_temp_tm, eup_thm)
   end;

  end;


  (*---------------*)
  (* Compute block *)
  (*---------------*)

  (* Simple eval *)

  val compute_bl_conv = SIMP_CONV list_ss [bir_is_lifted_inst_block_COMPUTE_block_def,
             bir_update_assert_block_def, pairTheory.pair_case_thm,
             bir_assert_block_def, bir_update_blockE_INIT_def, bir_update_blockB_def,
             bir_updateE_desc_remove_var_def, bir_updateE_desc_var_def,
             bir_updateB_desc_use_temp_def,
             bir_update_blockB_STEP1_def,
             bir_temp_varsTheory.bir_temp_var_def,
             bir_assert_desc_exp_def,
             bir_update_blockB_STEP2_def,
             bir_update_blockE_FINAL_def]
  fun compute_bl lb al_mem_t al_step_t eup_temp_t eup_t updates_t = let
    val bl0_tm = list_mk_comb (bir_is_lifted_inst_block_COMPUTE_block_tm,
        [lb, al_mem_t, al_step_t, eup_temp_t, eup_t, updates_t]);
    val bl_thm = compute_bl_conv bl0_tm
    val bl_t = rhs (concl bl_thm)
  in (bl_t, bl_thm) end;


  (*-------------------------------*)
  (* Combine it all, main function *)
  (*-------------------------------*)

  (* DEBUG

     val (lb, ms_case_cond_t, next_thm) = el 1 sub_block_work_list
  *)

  (* This is the main workhorse. It gets a single next theorem and tries to
     instantiate inst_thm to generate a block mimicking this next_thm. The
     block should use label "lb" and extra condition "ms_case_cond_t" can be assumed. *)
  fun lift_single_block inst_lift_thm0 bir_is_lifted_inst_block_COMPUTE_precond_tm0
     mu_thm (lb, ms_case_cond_t, next_thm) = let
     val next_thm0 = REWRITE_RULE [ASSUME ms_case_cond_t] next_thm
     fun raiseErr s = raise (bir_inst_liftingAuxExn (BILED_msg s));

     (* compute ms' and al_step *)
     val (ms'_t, al_step_t, ms'_thm) = compute_al_step_ms' next_thm0
       handle HOL_ERR _ => raiseErr "computing al_step and ms' failed";

     (* next compute imm_ups *)
     val (imm_ups_t, imm_ups_thm) = compute_imm_ups ms'_t
       handle HOL_ERR _ => raiseErr "computing imm_ups failed";

     (* compute eup *)
     val (eup_t, eup_THM) = compute_eup ms'_t
       handle HOL_ERR _ => raiseErr "computing eup failed";

     (* compute mem_up *)
     val (mem_up_t, real_mem_up_opt, mem_up_thm) = compute_mem_up ms'_t
       handle HOL_ERR _ => raiseErr "computing mem_up failed";

     (* compute al_mem *)
     val (al_mem_t, al_mem_THM) = compute_al_mem ms'_t mu_thm real_mem_up_opt mem_up_thm
       handle HOL_ERR _ => raiseErr "computing al_mem failed";

     (* Now we need to compute the updates. This involves lifting of all computed immediates
        in imm_ups and checking whether the vars don't interfer with each other. *)
     val (updates_t, eup_temp_t, updates_THM) = compute_updates mem_up_t imm_ups_t eup_t
       handle HOL_ERR _ => raiseErr "computing updates failed";

     (* compute bl *)
     val (bl_t, bl_thm) = compute_bl lb al_mem_t al_step_t eup_temp_t eup_t updates_t
       handle HOL_ERR _ => raiseErr "computing bl failed";

     (* derive the precond *)
     val precond_thm = let
       val tm0 = list_mk_comb (bir_is_lifted_inst_block_COMPUTE_precond_tm0,
         [bl_t, lb, mk_abs (ms_v, ms_case_cond_t)])

       val ex_insts = [ms'_t, al_step_t, imm_ups_t, mem_up_t, al_mem_t,
         eup_t, eup_temp_t, updates_t]

       val tm1 = list_mk_comb (tm0, ex_insts)

       val thm0 = EQT_ELIM (SIMP_CONV std_ss [bir_is_lifted_inst_block_COMPUTE_precond_def,
         al_mem_THM, updates_THM, bl_thm, eup_THM, mem_up_thm,
         imm_ups_thm, ms'_thm] tm1)

       val tm_goal = list_mk_exists (inst_lift_THM_ex_vars,
          list_mk_comb (tm0, inst_lift_THM_ex_vars));

       val thm1 = prove (``^tm_goal``,
         EVERY (List.map EXISTS_TAC ex_insts) >>
         REWRITE_TAC [thm0]);

       val thm2 = GENL [ms_v, bs_v] thm1
     in thm2 end
       handle HOL_ERR _ => raiseErr "proving precondition of theorem failed";

    val final_thm = let
       val thm0 = SPECL [mk_abs (ms_v, ms_case_cond_t), bl_t, lb] inst_lift_thm0
       val thm1 = MP thm0 precond_thm
    in thm1 end handle HOL_ERR _ => raiseErr "proving final thm failed! Does the block still depend on ms and bs, i.e. is not completely evaluated?";
  in
    final_thm
  end handle HOL_ERR _ => raise (bir_inst_liftingAuxExn (BILED_msg "???"));


  (**************************)
  (* Lifting an instruction *)
  (**************************)

  (* This is the main entry point for lifting an instruction. Given

     - a memory region not to touch
     - the hex-code of an instruction
     - and a PC in form of a number to load it from


     a program consisting of one or multiple blocks is produced that corresponds to
     executing the machine instruction and does not touch the memory region.

     The program starts at a block with a label corresponding to the PC. All other labels are
     not numeric (BL_Address) labels but string (BL_Label) label whose stringt starts with a
     prefix derived from the address. *)

  fun bir_lift_instr_mu (mu_thm:thm) (pc : Arbnum.num) hex_code =
  let
     (* call step lib to generate step theorems, compute mm and label *)
     val (next_thms, mm_tm, label_tm) = mk_inst_lifting_theorems pc hex_code

     (* instantiate inst theorem *)
     val inst_lift_thm0 = let
       val thm0 = MATCH_MP inst_lift_THM mu_thm
       val thm1 = SPECL [mm_tm, label_tm] thm0
       val (pre, _) = dest_imp_only (concl thm1)
       val pre_thm = prove (pre,
          SIMP_TAC (list_ss++wordsLib.WORD_ss) [WF_bmr_ms_mem_contains_def,
            bmr_ms_mem_contains_interval_def, WI_size_def, WI_is_sub_compute, WI_wf_def]);
       val thm2 = MP thm1 pre_thm
     in thm2 end;

     val bir_is_lifted_inst_block_COMPUTE_precond_tm0 =
       list_mk_comb (bir_is_lifted_inst_block_COMPUTE_precond_tm_mr,
        [label_tm, (rand (concl mu_thm)), mm_tm])

     (* preprocess next-theorems. Merge some, order them, derive conditions,
        assign auxiliary labels, ... *)
     val sub_block_work_list = preprocess_next_thms label_tm pc next_thms

     val sub_block_thms = map (lift_single_block inst_lift_thm0 bir_is_lifted_inst_block_COMPUTE_precond_tm0 mu_thm) sub_block_work_list

     (* TODO: implement merging *)
     val _ = if (length sub_block_thms = 1) then () else failwith "TODO";
  in
     hd sub_block_thms
  end handle bir_inst_liftingAuxExn d =>
    raise (bir_inst_liftingExn (hex_code, d));


  fun bir_lift_instr ((mu_b : Arbnum.num), (mu_e : Arbnum.num)) = let
     val (_, mu_thm) = mk_WI_end_of_nums_WFE addr_sz_ty mu_b mu_e
  in
    bir_lift_instr_mu mu_thm
  end;

end

structure bir_inst_liftingLib = struct

  structure bmil_arm8 = bir_inst_liftingFunctor (struct val mr = arm8_bmr_rec end);

end
