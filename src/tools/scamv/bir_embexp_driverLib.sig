signature bir_embexp_driverLib = sig

  (* Inputs:
       - (architecture_id, prog_gen_id)
       - asm_lines
     Returns id of program entry (prog_id)
   *)
  val bir_embexp_prog_create : (string * string) -> string list -> string

  (* Inputs:
       - (architecture_id, experiment_type_id/attacker_id, state_gen_id/obs_model_id)
       - prog_id (see above)
       - (state1, state2)
     Returns experiment id (exp_id)
   *)
  val bir_embexp_sates2_create : (string * string * string) -> string -> (((string * num) list) * ((string * num) list)) -> string

  (* Inputs:
       - exp_id (see above)
       - with_reset (run with reset or not)
     Returns (maybe result, comment)
   *)
  val bir_embexp_run : string -> bool -> (bool option * string)

end
