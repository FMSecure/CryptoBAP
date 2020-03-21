signature bir_conc_execLib = sig

  datatype modelValues = memT of (string * (num*num) list)
		       | regT of (string * num)
  val conc_exec_program :  int -> term -> (term -> term) option -> (num * num) list -> term

  val conc_exec_obs_extract : term -> term list

  val conc_exec_obs_compute : term -> modelValues list -> term list
  val conc_exec_obs_compare : term -> modelValues list * modelValues list -> bool

end
