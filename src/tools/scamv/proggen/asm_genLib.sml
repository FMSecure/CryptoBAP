structure asm_genLib : asm_genLib =
struct

open qc_genLib;
infix 5 <$>;
infix 5 >>=;

datatype BranchCond = EQ | NE | LT | GT
datatype Operand =
           Imm of int
         | Ld  of int option * string
         | Reg of string
datatype ArmInstruction =
           Load    of Operand * Operand
         | Store   of Operand * Operand
         | Branch  of BranchCond option * Operand
         | Compare of Operand * Operand
         | Nop
         | Add     of Operand * Operand * Operand
	 | Lsl     of Operand * Operand * Operand

(* pp *)
local
fun pp_operand (Imm n) = "#0x" ^ Int.fmt StringCvt.HEX n
  | pp_operand (Ld (NONE, src)) = "[" ^ src ^ "]"
  | pp_operand (Ld (SOME offset, src)) =
    "[" ^ src ^ ", #" ^ Int.toString offset ^ "]"
  | pp_operand (Reg str) = str

fun pp_opcode (Load _)    = "ldr"
  | pp_opcode (Store _)  = "str"
  | pp_opcode (Branch _)  = "b"
  | pp_opcode (Compare _) = "cmp"
  | pp_opcode (Nop)       = "nop"
  | pp_opcode (Add _)     = "add"
  | pp_opcode (Lsl _)     = "lsl"

fun pp_cond bc =
    case bc of
        EQ => "eq"
      | NE => "ne"
      | LT => "lt"
      | GT => "gt"

fun pp_instr instr =
    case instr of
        Load (target,source) =>
        pp_opcode instr ^ " " ^ pp_operand target ^ ", "
        ^ pp_operand source
     | Store (source, target) =>
        pp_opcode instr ^ " " ^ pp_operand source ^ ", "
        ^ pp_operand target
     |  Branch (NONE, target) =>
        "b " ^ pp_operand target
     | Branch (SOME cond, target) =>
       "b." ^ pp_cond cond ^ " " ^ pp_operand target
     | Compare (a, b) =>
       "cmp " ^ pp_operand a ^ ", " ^ pp_operand b
     | Nop =>
       "nop"
     | Add (target, a, b) =>
       "add " ^ pp_operand target ^ ", " ^ pp_operand a ^ ", " ^ pp_operand b
     | Lsl (target,source ,b) =>
       "lsl " ^ pp_operand target ^ ", " ^ pp_operand source ^ ", " ^ pp_operand b
in
fun pp_program is = List.map pp_instr is;
end

(* arb instances *)
local
    val min_addr = 0x1000;
    val max_addr = 0x2000;
in
val arb_addr = choose (min_addr, max_addr);

val arb_armv8_regname =
    let
        fun regs n = List.tabulate (n, fn x => "x" ^ (Int.toString x))
    in
        elements (regs 30)
    end;

val arb_imm = Imm <$> arb_addr;
val arb_reg = Reg <$> arb_armv8_regname;
val arb_operand =
    frequency
        [(1, arb_imm)
        ,(5, arb_reg)]

val arb_branchcond =
    let val arb_cond = elements [EQ, NE, LT, GT];
    in
        arb_option arb_cond
    end;

val arb_ld = Ld <$> two (arb_option (elements [4,8,16])) arb_armv8_regname;

val arb_load_indir = Load <$> (two arb_reg arb_ld);
val arb_load_pcimm = Load <$> (two arb_reg arb_imm);
val arb_load = oneof [arb_load_indir, arb_load_pcimm];

val arb_store_indir = Store <$> (two arb_reg arb_ld);
val arb_store_pcimm = Store <$> (two arb_reg arb_imm);
val arb_store = oneof [arb_store_indir, arb_store_pcimm];

val arb_branch = Branch <$> (two arb_branchcond arb_imm);
val arb_compare = Compare <$> (two arb_reg arb_reg);
val arb_nop = return Nop;
val arb_add = (fn (t, (a, b)) => Add (t,a,b)) <$> (two arb_reg (two arb_reg arb_reg));

val arb_instruction_noload_nobranch =
    frequency
        [(1, arb_compare)
        ,(1, arb_nop)
        ,(1, arb_add)]

val arb_program_noload_nobranch = arb_list_of arb_instruction_noload_nobranch;

val arb_program_load = arb_list_of arb_load_indir;

fun arb_program_cond arb_prog_left arb_prog_right =
  let
    fun rel_jmp_after bl = Imm (((length bl) + 1) * 4);

    val arb_prog      = arb_prog_left  >>= (fn blockl =>
                        arb_prog_right >>= (fn blockr =>
                        arb_compare    >>= (fn cmp    =>
                           let val blockl_wexit = blockl@[Branch (NONE, rel_jmp_after blockr)] in
                             return ([cmp, Branch (SOME EQ, rel_jmp_after blockl_wexit)]
                                    @blockl_wexit
                                    @blockr)
                           end
                        )));
  in
    arb_prog
  end;

val arb_program_previct1 =
  let
    val arb_pad = sized (fn n => choose (0, n)) >>=
                  (fn n => resize n arb_program_noload_nobranch);

    val arb_load_instr = arb_load_indir;

    val arb_block_3ld = (List.foldr (op@) []) <$> (
                        sequence [arb_pad, (fn x => [x]) <$> arb_load_instr
                                 ,arb_pad, (fn x => [x]) <$> arb_load_instr
                                 ,arb_pad, (fn x => [x]) <$> arb_load_instr
                                 ,arb_pad]);
  in
    arb_program_cond arb_block_3ld arb_block_3ld
  end;

val arb_program_previct2 =
  let
    val arb_pad = sized (fn n => choose (0, n)) >>=
                  (fn n => resize n arb_program_noload_nobranch);

    val arb_load_instr = arb_load_indir;

    val arb_block_3ld = (List.foldr (op@) []) <$> (
                        sequence [(fn x => [x]) <$> arb_load_instr
                                 ,arb_pad
                                 ,(fn x => [x]) <$> arb_load_instr
                                 ,(fn x => [x]) <$> arb_load_instr
                                 ]);
  in
    arb_program_cond arb_block_3ld arb_block_3ld
  end;

val arb_program_previct3 =
  let
    val arb_pad = sized (fn n => choose (0, n)) >>=
                  (fn n => resize n arb_program_noload_nobranch);

    val arb_load_instr = arb_load_indir;

    val arb_leftright =
      arb_load_instr >>= (fn ld1 =>
      arb_load_instr >>= (fn ld2 =>
      arb_load_instr >>= (fn ld3 =>
        let val arb_block_3ld =
                        (List.foldr (op@) []) <$> (
                        sequence [return [ld1]
                                 ,arb_pad
                                 ,return [ld2]
                                 ,return [ld3]
                                 ]) in
          two arb_block_3ld arb_block_3ld
        end
      )));
  in
    arb_leftright >>= (fn (l,r) => arb_program_cond (return l) (return r))
  end;

val arb_program_previct4 =
  let
    val arb_pad = sized (fn n => choose (0, n)) >>=
                  (fn n => resize n arb_program_noload_nobranch);

    val arb_load_instr = arb_load_indir;

    val arb_leftright =
      arb_load_instr >>= (fn ld1 =>
      arb_load_instr >>= (fn ld2 =>
      arb_load_instr >>= (fn ld3 =>
        let val arb_block_3ld =
                        (List.foldr (op@) []) <$> (
                        sequence [return [ld1]
                                 ,arb_pad
                                 ,return [ld2]
                                 ,return [ld3]
                                 ]) in
          two (return [ld1, ld2, ld3]) arb_block_3ld
        end
      )));
  in
    arb_leftright >>= (fn (l,r) => arb_program_cond (return l) (return r))
  end;

val arb_program_previct5 =
  let
    val arb_pad = sized (fn n => choose (0, n)) >>=
                  (fn n => resize n (arb_list_of arb_nop));

    val arb_load_instr = arb_load_indir;

    val arb_leftright =
      arb_load_instr >>= (fn ld1 =>
      arb_load_instr >>= (fn ld2 =>
      arb_load_instr >>= (fn ld3 =>
        let val arb_block_3ld =
                        (List.foldr (op@) []) <$> (
                        sequence [return [ld1]
                                 ,arb_pad
                                 ,return [ld2]
                                 ,return [ld3]
                                 ]) in
          two (return [ld1, ld2, ld3]) arb_block_3ld
        end
      )));
  in
    arb_leftright >>= (fn (l,r) => arb_program_cond (return l) (return r))
  end;
end


(* ================================ *)
fun prog_gen_a_la_qc_gen do_resize gen n =
    let
      val g = bir_randLib.rand_gen_get ();
      val (p, _) = run_step n g (if do_resize then (resize n gen) else gen);
    in
        pp_program p
    end;

val prog_gen_a_la_qc =
    prog_gen_a_la_qc_gen true;

val prog_gen_a_la_qc_noresize =
    prog_gen_a_la_qc_gen false;


(*=========== Spectre Gen ========+=*)
local
  fun arb_regname_except xs =
    such_that (fn r => not (exists (fn x => x = r) xs)) arb_armv8_regname;

  fun arb_ld_offset reg offset =
    arb_regname_except [reg] >>= (fn source =>
    return (Load (Reg reg, Ld (SOME offset, source))));

  fun arb_ld_offset_src reg offset =
    arb_regname_except [reg] >>= (fn source => 
    return (source, Load (Reg reg, Ld (SOME offset, source))))

  fun arb_ld_reg_src reg =
    arb_regname_except [reg] >>= (fn source => 
    arb_regname_except [reg] >>= (fn reg'   =>
      return (source, Load (Reg reg, Ld (NONE, source^","^reg')))));

  fun arb_ld_offset_selected_source reg  offset =
    arb_regname_except [reg] >>= (fn target =>
    return (target, Load (Reg target, Ld (SOME offset, reg))));

  fun arb_str_offset_selected_target reg offset =
    arb_regname_except [reg] >>= (fn source =>
    return (source, Store (Reg source, Ld (SOME offset, reg))));

  fun arb_mem_op_selected_source  reg  offset   =
    oneof[arb_ld_offset_selected_source reg offset, arb_str_offset_selected_target reg offset];

  fun arb_shift_left_selected_source reg offset =
      return (Lsl (Reg reg, Reg reg, Imm offset));

  val arb_pad = sized (fn n => choose (0, n)) >>=
		      (fn n => resize n arb_program_noload_nobranch);

  fun arb_cmp_g reg1 reg2 =
    return (Compare (Reg reg1, Reg reg2));

  fun arb_cmp () =
    let
	val offsets = repeat 2 (choose(0, 255))
	val regs    = repeat 2 (arb_regname_except ["x1", "x0"])
	val zipped  = regs >>= (fn reg => offsets >>= (fn off =>  return ((zip reg off), reg)))
    in
	
        zipped >>= (fn (pairs, [reg1, reg2]) => sequence((map (fn (r,i) => arb_ld_offset r i) pairs)@[arb_cmp_g reg1 reg2])
	       >>= (fn result => return (result)))
    end;

  fun arb_cmp_r () =
    let
	val offsets = choose(0, 255)
	val regs    = arb_regname_except ["x1", "x0"];
	val zipped  = regs >>= (fn reg1 => offsets 
			   >>= (fn off => arb_regname_except [reg1]
                           >>= (fn reg2 =>  return ([(reg1, off)], [reg1,reg2]))));
    in
	
        zipped >>= (fn (pairs, [reg1, reg2]) => sequence((map (fn (r,i) => arb_ld_offset r i) pairs)@[arb_cmp_g reg1 reg2])
	       >>= (fn result => return (result)))
    end;

  fun preamble () =
    let
	val offsets = choose(0, 255);
	val regs    = arb_regname_except ["x1", "x0"];
	val zipped  = regs >>= (fn reg1 => offsets 
			   >>= (fn off1 => arb_regname_except [reg1]
                           >>= (fn reg2 => offsets
		           >>= (fn off2 => return ([(reg1, off1), (reg2, off2)], [reg1,reg2])))));
    in
	
        zipped >>= (fn (pairs, [reg1, reg2]) => sequence((map (fn (r,i) => arb_ld_offset r i) pairs)@[arb_cmp_g reg1 reg2])
	       >>= (fn result => return (result, [reg1, reg2])))
    end;


  fun preamble1 () =
    let
	val offsets = choose(0, 255)
	val regs    = arb_regname_except ["x1", "x0"]
	val zipped  = regs >>= (fn reg1 => offsets 
			   >>= (fn off1 => arb_regname_except [reg1]
                           >>= (fn reg2 => offsets
		           >>= (fn off2 => return ([(reg1, off1), (reg2, off2)], [reg1,reg2])))))
	val ext_src = zipped >>= (fn (pairs, [reg1,reg2]) => sequence (map (fn (r,i) => arb_ld_offset_src r i) pairs)
			     >>= (fn h::t::_ => (return ([fst h, fst t], [snd h, snd t], [reg1, reg2]))
				 ))
    in
	ext_src >>= (fn (srcs, lds, [reg1, reg2]) =>  (arb_cmp_g (hd srcs) reg2)
                >>= (fn cmpi => return (lds@[cmpi], [reg1, reg2])))
    end;

  fun preamble2 () =
    let
	val offsets = choose(0, 255)
	val regs    = arb_regname_except ["x1", "x0"]
	val zipped  = regs >>= (fn reg1 => offsets 
			   >>= (fn off1 => arb_regname_except [reg1]
                           >>= (fn reg2 => return ([(reg1, off1), (reg2, 0)], [reg1,reg2]))))

	val ext_src = zipped >>= (fn (p1::p2::_ , [reg1, reg2]) =>
                                         sequence ([arb_ld_reg_src (fst p1), arb_ld_offset_src (fst p2) (snd p2)])
			     >>= (fn h::t::_ => (return ([fst h, fst t], [snd h, snd t], [reg1, reg2]))))
    in
	ext_src >>= (fn (srcs, lds, [reg1, reg2]) =>  (arb_cmp_g (hd srcs) reg2)
                >>= (fn cmpi => return (lds@[cmpi], [reg1, reg2])))
    end;

  fun left_gen reg offset =
      (arb_ld_offset_selected_source reg  offset)
              >>= (fn (_, mop) => return [mop])
      (* (arb_ld_offset_selected_source reg  offset)  *)
               (* >>= (fn (reg, ld1) => arb_shift_left_selected_source  reg 9 *)
               (* >>= (fn   shift    => arb_mem_op_selected_source reg offset *)
               (* >>= (fn (_,   ld2) => return [ld1, shift, ld2]))) *);
      
  val arb_block_l = 
      let 
	  val offsets = choose(0, 255)
      in
    preamble() >>= (fn (prmbl, [reg1, _]) => offsets 
               >>= (fn offset => ((List.foldr (op@) []) <$> 
   	            (sequence [arb_pad, (left_gen reg1 offset)]))
               >>= (fn left => return (prmbl, left))))
      end;

  val arb_block_l2 = 
      let 
	  val offsets = choose(0, 255)
      in
    preamble1() >>= (fn (prmbl, regs) => offsets 
	       >>= (fn offset =>  arb_regname_except regs
               >>= (fn reg1 => ((List.foldr (op@) []) <$> 
   	            (sequence [(* arb_pad, *) (left_gen reg1 offset)]))
               >>= (fn left => return (prmbl, left)))))
      end;

  val arb_block_l3 = 
      let 
	  val offsets = choose(0, 255)
      in
    preamble2() >>= (fn (prmbl,  [reg1, reg2]) => offsets 
               >>= (fn offset => ((List.foldr (op@) []) <$> 
   	             (sequence [(left_gen reg1 offset)]))
               >>= (fn left => return (prmbl, left))))
      end;

in
  fun arb_program_cond_spectre preamble arb_prog_left arb_prog_right =
      let
  	  fun rel_jmp_after bl = Imm (((length bl) + 1) * 4);

  	  val arb_prog =arb_prog_left  >>= (fn blockl =>
                        arb_prog_right >>= (fn blockr =>
                        preamble       >>= (fn prmbl  =>
                           let val blockl_wexit = blockl@[Branch (NONE, rel_jmp_after blockr)] in
                             return (prmbl
  			            @[Branch (SOME EQ, rel_jmp_after blockl_wexit)]
                                    @blockl_wexit
                                    @blockr)
                           end
                        )));
      in
  	  arb_prog
      end;

  (* val arb_program_spectre = *)
  (*     let *)
  (* 	  val arb_pad = sized (fn n => choose (0, n)) >>= *)
  (* 			      (fn n => resize n arb_program_noload_nobranch); *)

  (* 	  val arb_load_instr = arb_load_indir; *)
  (* 	  val arb_store_instr= arb_store_indir; *)

  (* 	  val arb_block_l = (List.foldr (op@) []) <$> ( *)
  (*                           sequence [arb_pad, (fn x => [x]) <$> oneof[arb_load_instr, arb_store_instr]]); *)

  (* 	  val arb_block_r = (List.foldr (op@) []) <$> ( *)
  (*                           sequence [arb_pad, (fn x => [x]) <$> oneof[arb_load_instr, arb_store_instr]]); *)
  (*     in *)
  (* 	  arb_program_cond_spectre (arb_cmp_r ()) arb_block_l arb_block_r *)
  (*     end; *)

  fun arb_program_glue_spectre arb_prog_preamble_left arb_prog_right =
      let
  	  fun rel_jmp_after bl = Imm (((length bl) + 1) * 4);

  	  val arb_prog =arb_prog_preamble_left >>= (fn (prmbl, blockl) =>
                        arb_prog_right >>= (fn blockr =>
            
                           let val blockl_wexit = blockl@[Branch (NONE, rel_jmp_after blockr)] in
                             return (prmbl
  			            @[Branch (SOME EQ, rel_jmp_after blockl_wexit)]
                                    @blockl_wexit
                                    @blockr)
                           end
                        ));
      in
  	  arb_prog
      end;
    
  val arb_program_spectre =
      let
  	  val offsets = choose(0, 255);
  	  val arb_load_instr  =  arb_load_indir;
  	  val arb_store_instr = arb_store_indir;


  	  val arb_block_r = (List.foldr (op@) []) <$> (
              sequence [(* arb_pad, *) (fn x => [x]) <$> oneof[arb_load_indir(* , arb_store_indir *)]]);
      in
  	  arb_program_glue_spectre arb_block_l3 arb_block_r
      end
      
end

end
