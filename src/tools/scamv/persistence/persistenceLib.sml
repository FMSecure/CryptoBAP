structure persistenceLib :> persistenceLib =
struct

  open HolKernel Parse boolLib bossLib;

  open bir_randLib;
  open bir_miscLib;

  open holba_entryLib;

  open experimentsLib;
  open embexp_logsLib;

  (* error handling *)
  val libname = "persistenceLib"
  val ERR = Feedback.mk_HOL_ERR libname
  val wrap_exn = Feedback.wrap_exn libname

  (* disable this for less outputs to the database *)
  val enable_log_outputs = true;


  (* creation of a holba run with metadata and containers for programs and experiments *)
  (* ========================================================================================= *)
  datatype holba_run_refs = RunReferences of (run_handle * string * prog_list_handle * exp_list_handle);
  fun get_dotfree_time () =
    let
      val now      = Time.now ();
      val now_ms   = LargeInt.mod (Time.toMilliseconds now, LargeInt.fromInt 1000)
      val now_ms_str = StringCvt.padLeft #"0" 4 (LargeInt.fmt StringCvt.DEC now_ms);
      val now_date = Date.fromTimeLocal now;
      val now_str  = (Date.fmt "%Y-%m-%d_%H-%M-%S" now_date) ^ "_" ^ now_ms_str;

     (* assert no dots in name *)
      val _ = if not (List.exists (fn x => x = #".") (String.explode now_str)) then () else
              raise ERR "get_dotfree_time" "should never happen, found a dot in the generated name";
    in
     (* time = time without dot *)
      now_str
    end;
  fun holba_run_create () =
    let
      val name      = get_dotfree_time ();

      val list_v  = LogsList ("HOLBA." ^ name, SOME "auto-generated");
      val prog_l_id = create_prog_list list_v;
      val exp_l_id  = create_exp_list  list_v;

      val run_v     = LogsRun (name, prog_l_id, exp_l_id);
      val run_id    = create_run run_v;

      (* prepare metadata for run *)
         (* write out git commit and git diff of current directory. *)
         (*    so this code needs to be executed with the working directory in the holbarepo! *)
      open bir_exec_wrapLib;
      val run_datestr    = get_datestring();
      val holba_diff     = get_exec_output "git diff";
      val holba_commit   = get_exec_output "git rev-parse HEAD";
      val holba_args     = get_script_args ();
      val rand_seed      = rand_seed_get ();
      val holba_randseed = Real.toString rand_seed;

      val run_metadata =
        [("time",     run_datestr),
         ("diff",     holba_diff),
         ("commit",   holba_commit),
         ("args",     holba_args),
         ("randseed", holba_randseed)];

      (* add metadata *)
      val _ = List.map (fn (m_n, m_v) => 
        init_meta (mk_run_meta_handle (run_id, SOME m_n, "")) (SOME m_v)) run_metadata;
    in
      RunReferences (run_id, name, prog_l_id, exp_l_id)
    end;

  (* logging of holba run data and run context management *)
  (* ========================================================================================= *)
  val holbarun_log = ref (NONE:meta_handle option);
  val prog_log     = ref (NONE:meta_handle option);
  val exp_log      = ref (NONE:meta_handle option);
  fun get_log_out (log, fun_name, err_msg) =
    case !log of
        NONE => raise ERR fun_name err_msg
      | SOME log_out => log_out;

  fun close_log log         = log := NONE;
  fun create_log log log_id =
    if not enable_log_outputs then () else
    let
      val _ = init_meta log_id (SOME "");
      val _ = log := SOME log_id;
    in () end;

  fun write_log_line log_t line =
    if not enable_log_outputs then () else
    let
      val log_id = get_log_out log_t;
      val _ = append_meta log_id (line ^ "\n");
    in () end;

  fun run_log_prog message =
    let
      val line = message;
    in
      write_log_line (prog_log, "run_log_prog", "no program log registered currently") line
    end;

  fun run_log_exp message =
    let
      val line = message;
    in
      write_log_line (exp_log, "run_log_exp", "no experiment log registered currently") line
    end;

  fun run_log_raw message =
    let
      val line = message;
    in
      write_log_line (holbarun_log, "run_log", "no holbarun log registered currently (this should never happen)") line
    end;

  (* embexp run references (database handles and special name string) *)
  val holba_run_id_ref    = ref (NONE:holba_run_refs option);
  val holba_run_timer_ref = ref (NONE:Time.time option);
  fun holba_run_id () =
    case !holba_run_id_ref of
        NONE =>
          let
            val run_refs = holba_run_create ();
            val RunReferences (run_id, run_name, _, _) = run_refs;

            val _ = create_log holbarun_log (mk_run_meta_handle (run_id, SOME "log", ""));
            val _ = write_log_line (holbarun_log, "holba_run_id", "no no no") ("Starting log for: " ^ run_name);

            val _ = holba_run_timer_ref := timer_start 1;
            val _ = holba_run_id_ref := SOME run_refs;
          in
            run_refs
          end
      | SOME p => p;

  fun run_log message =
    let
      val _ = holba_run_id ();
      val _ = run_log_raw message;
    in
      ()
    end;

  fun run_finalize () =
    let
      val _ = holba_run_id ();
      val _ = timer_stop (fn d_time =>
               run_log_raw ("\n\n======================================\n" ^
                                   "Experiment generation duration: " ^ d_time)
              ) (!holba_run_timer_ref);

      val _ = holba_run_id_ref := NONE;
      val _ = holba_run_timer_ref := NONE;
    in
      close_log holbarun_log
    end;


  (* storing to logs *)
  (* ========================================================================================= *)
  fun run_create_prog arch prog run_metadata =
    let
      val arch_id = exp_arch_to_string arch;

      val RunReferences (_, run_name, prog_l_id, _) = holba_run_id();

      val asm_code = prog_to_asm_code prog;
      val prog_v   = LogsProg (arch_id, asm_code);
      val prog_id  = create_prog prog_v;
      val _        = add_to_prog_list (prog_l_id, prog_id);

      val meta_name = "run." ^ run_name ^ "." ^ (get_dotfree_time ());

      (* add metadata *)
      val _ = List.map (fn (m_n, m_v) => 
        init_meta (mk_prog_meta_handle (prog_id, SOME m_n, meta_name)) (SOME m_v)) run_metadata;

      (* create prog log, NOTICE: this is never closed (also not needed at the moment) *)
      val _ = create_log prog_log (mk_prog_meta_handle (prog_id, SOME "log", meta_name));
    in
      prog_id
    end;

  fun run_create_exp prog_id exp_type exp_params state_list run_metadata =
    let
      val exp_type_s = exp_type_to_string exp_type;

      val RunReferences (_, run_name, _, exp_l_id) = holba_run_id();

      val input_data = Json.OBJECT (List.map (fn (n, s) => ("input_" ^ n, machstate_to_Json s)) state_list);
      val exp_v      = LogsExp (prog_id, exp_type_s, exp_params, input_data);
      val exp_id     = create_exp exp_v;
      val _          = add_to_exp_list (exp_l_id, exp_id);

      val meta_name = "run." ^ run_name ^ "." ^ (get_dotfree_time ());

      (* add metadata *)
      val _ = List.map (fn (m_n, m_v) => 
        init_meta (mk_exp_meta_handle (exp_id, SOME m_n, meta_name)) (SOME m_v)) run_metadata;

      (* create exp log, NOTICE: this is never closed (also not needed at the moment) *)
      val _ = create_log exp_log (mk_exp_meta_handle (exp_id, SOME "log", meta_name));

    in
      exp_id
    end;


  (* retrieving from logs *)
  (* ========================================================================================= *)
  fun runlogs_load_progs listname =
    let
      val prog_l_ids = query_all_prog_lists ();
      val prog_ls = get_prog_lists prog_l_ids;

      val (_, prog_ls_) = List.foldl (fn (x, (i, l)) => (i+1, ((i, x))::l)) (0, []) prog_ls;
      val prog_ls_filt = List.filter (fn (_, LogsList (n, _)) => n = listname) prog_ls_;
      val (i, _) = if List.length prog_ls_filt = 1 then hd prog_ls_filt else
                    raise ERR "runlogs_load_progs" ("didn't find exactly one match for prog list " ^ listname);
      val prog_l_id = List.nth (prog_l_ids, i);

      val prog_ids = get_prog_list_entries prog_l_id;

      val progs = List.map (fn (LogsProg (_,code)) => prog_from_asm_code code) (get_progs prog_ids);
    in
      progs
    end;

end

