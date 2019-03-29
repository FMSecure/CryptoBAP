structure bir_embexp_driverLib =
struct

  local

  open HolKernel Parse boolLib bossLib;

  in

(*
  val s1 = [("R1", 0), ("R2", 0)];
  val s2 = [("R1", 0), ("R2", 32*1024)];
  bir_embexp_run_cache_distinguishability s1 s2;
*)

  fun set_entropy_input_h s1 s2 =
    let
      val (x1_s_1, x1_1) = hd s1;
      val (x1_s_2, x1_2) = hd s2;

      val _ = if x1_s_1 <> "R1" andalso
                 x1_s_2 <> "R1" then
               raise ERR "set_entropy_input_h" "input wrong"
              else ();

      val str = "state_input state1 = {\n" ^
                "\t.x1 = " ^ (Int.toString x1_1) ^ ",\n" ^
                "\t.x2 = 0x0, .x3 = 0x0" ^
                "};\n" ^
                "\n" ^
                "state_input state2 = {\n" ^
                "\t.x1 = " ^ (Int.toString x1_1) ^ ",\n" ^
                "\t.x2 = 0x0, .x3 = 0x0" ^
                "};\n";

      val file = TextIO.openOut "../../../../../EmbExp-ProgPlatform/src/entropy_input.h";
      val _    = TextIO.output (file, str);
      val _    = StreamIO.closeOut file;
    in
      ()
    end;

  fun create_setup_asm_prelude s =
    let
      (* assert that the value can be set in this way and is not too big *)
      val _ = if (value > 1024*1024) then raise ERR "create_setup_asm_prelude" "value cannot be set" else ();

      fun set_reg_asm (reg_name, value) = "\tSET " ^ reg_name ^ ", #" ^ (Int.toString value);
      val set_reg_asm_list = List.map set_reg_asm s;
    in
      List.foldr (fn (s,acc) => acc ^ s ^ "\n") "" set_reg_asm_list
    end;

  (* make connect has to be run before and must be complete *)
  fun bir_embexp_run_cache_distinguishability test_asm s1 s2 =
    let
      val s1_prelude = create_setup_asm_prelude s1;
      val s2_prelude = create_setup_asm_prelude s2;

      (* compose preludes and test_asm in the src directory *)

      (* TODO: remove this later *)
      val _ = set_entropy_input_h s1 s2;

      (* make runlog *)
      val _ = OS.Process.system ("make --directory=../../../../../EmbExp-ProgPlatform runlog");

      (* evaluate uart.log *)
      val file = TextIO.openIn "../../../../../EmbExp-ProgPlatform/temp/uart.log";
      val _    = TextIO.input (file, str);
      fun allLinesRevFun acc = case inputLine file of
			  | NONE => acc
			  | SOME l => allLinesFun (l::acc);
      val _    = StreamIO.closeIn file;
      val lastline = hd (allLinesRevFun []);

    in
      true (* return result from evaluation *)
    end;

  end (* local end *)

end

