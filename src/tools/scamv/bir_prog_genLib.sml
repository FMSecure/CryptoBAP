structure bir_prog_genLib :> bir_prog_genLib =
struct

local
  open HolKernel boolLib liteLib simpLib Parse bossLib;
  open arm8_progLib arm8AssemblerLib arm8;
in

  local
    val mock_progs_i = ref 0;
    val mock_progs = ref [["ldr x2, [x1]"]];
    val wrap_around = ref false;
  in
    fun bir_prog_gen_arm8_mock_set progs =
      let
        val _ = mock_progs_i := 0;
        val _ = mock_progs := progs;
      in
	()
      end;

    fun bir_prog_gen_arm8_mock_set_wrap_around b =
      let
        val _ = wrap_around := b;
        val _ = if not (!wrap_around) then ()
                else mock_progs_i := Int.mod(!mock_progs_i, length (!mock_progs));
      in
	()
      end;

    fun bir_prog_gen_arm8_mock () =
      let
        val _ = if !mock_progs_i < length (!mock_progs) then ()
                else raise ERR "bir_prog_gen_arm8_mock" "no more programs";

        val prog = List.nth(!mock_progs, !mock_progs_i);

        val _ = mock_progs_i := (!mock_progs_i) + 1;
        val _ = if not (!wrap_around) then ()
                else mock_progs_i := Int.mod(!mock_progs_i, length (!mock_progs));
      in
        prog
      end;
  end


 val arm8_names_weighted = [(0,"Address"),
  (1,"AddSubShiftedRegister32-1"),      (1,"AddSubShiftedRegister32-2"),     (1,"AddSubShiftedRegister32-3"),
  (1,"AddSubShiftedRegister32-4"),      (1,"AddSubShiftedRegister64-1"),     (1,"AddSubShiftedRegister64-2"),
  (1,"AddSubShiftedRegister64-3"),      (1,"AddSubShiftedRegister64-4"),     (1,"AddSubExtendRegister-1"),
  (1,"AddSubExtendRegister-2"),         (1,"AddSubExtendRegister-3"),        (1,"AddSubExtendRegister-4"),
  (1,"AddSubExtendRegister-5"),         (1,"AddSubExtendRegister-6"),        (1,"AddSubExtendRegister-7"),
  (1,"AddSubExtendRegister-8"),         (1,"AddSubImmediate-1"),             (1,"AddSubImmediate-2"),
  (1,"AddSubImmediate-3"),              (1,"AddSubImmediate-4"),             (1,"AddSubImmediate-5"),
  (1,"AddSubImmediate-6"),              (1,"AddSubImmediate-7"),             (1,"AddSubImmediate-8"),
  (1,"AddSubCarry-1"),                  (1,"AddSubCarry-2"),                 (1,"AddSubCarry-3"),
  (1,"AddSubCarry-4"),                  (1,"LogicalShiftedRegister32-1"),    (1,"LogicalShiftedRegister32-2"),
  (1,"LogicalShiftedRegister32-3"),     (1,"LogicalShiftedRegister32-4"),    (1,"LogicalShiftedRegister64-1"),
  (1,"LogicalShiftedRegister64-2"),     (1,"LogicalShiftedRegister64-3"),    (1,"LogicalShiftedRegister64-4"),
  (1,"LogicalImmediate32-1"),           (1,"LogicalImmediate32-2"),          (1,"LogicalImmediate32-3"),
  (1,"LogicalImmediate32-4"),           (1,"LogicalImmediate64-1"),          (1,"LogicalImmediate64-2"),
  (1,"LogicalImmediate64-3"),           (1,"LogicalImmediate64-4"),          (1,"Shift-1"),
  (1,"Shift-2"),                        (1,"MoveWide32"),                    (1,"MoveWide64"),
  (1,"BitfieldMove32"),                 (1,"BitfieldMove64"),                (0,"ConditionalCompareImmediate-1"),
  (1,"ConditionalCompareImmediate-2"),  (1,"ConditionalCompareImmediate-3"), (1,"ConditionalCompareImmediate-4"),
  (1,"ConditionalCompareRegister-1"),   (14,"ConditionalCompareRegister-2"), (14,"ConditionalCompareRegister-3"),
  (1,"ConditionalCompareRegister-4"),   (1,"ConditionalSelect-1"),           (14,"ConditionalSelect-2"),
  (1,"CountLeading-1"),                 (1,"CountLeading-2"),                (1,"ExtractRegister32"),
  (1,"ExtractRegister64"),              (1,"Division-1"),                    (1,"Division-2"),
  (1,"MultiplyAddSub-1"),               (1,"MultiplyAddSub-2"),              (1,"MultiplyAddSubLong"),
  (1,"MultiplyHigh"),                   (1,"Reverse32"),                     (1,"Reverse64"),
  (1,"CRC8"),                           (1,"CRC16"),                         (1,"CRC32"),
  (1,"CRC64"),                          (1,"BranchConditional"),             (1,"BranchImmediate-1"),
  (1,"BranchImmediate-2"),              (1,"BranchRegisterJMP"),             (1,"BranchRegisterCALL"),
  (1,"BranchRegisterRET"),              (1,"CompareAndBranch-1"),            (1,"CompareAndBranch-2"),
  (1,"TestBitAndBranch-1"),             (1,"TestBitAndBranch-2"),            (1,"TestBitAndBranch-3"),
  (1,"TestBitAndBranch-4"),             (1,"LoadStoreImmediate-1-1"),        (1,"LoadStoreImmediate-1-2"),
  (1,"LoadStoreImmediate-1-3"),         (1,"LoadStoreImmediate-1-4"),        (1,"LoadStoreImmediate-1-5"),
  (1,"LoadStoreImmediate-1-6"),         (1,"LoadStoreImmediate-1-7"),        (1,"LoadStoreImmediate-1-8"),
  (1,"LoadStoreImmediate-1-9"),         (1,"LoadStoreImmediate-1-10"),       (1,"LoadStoreImmediate-1-11"),
  (1,"LoadStoreImmediate-1-12"),        (1,"LoadStoreImmediate-1-13"),       (1,"LoadStoreImmediate-1-14"),
  (1,"LoadStoreImmediate-1-15"),        (1,"LoadStoreImmediate-1-16"),       (1,"LoadStoreImmediate-1-17"),
  (1,"LoadStoreImmediate-1-18"),        (1,"LoadStoreImmediate-1-19"),       (1,"LoadStoreImmediate-1-20"),
  (1,"LoadStoreImmediate-1-21"),        (1,"LoadStoreImmediate-1-22"),       (1,"LoadStoreImmediate-1-23"),
  (1,"LoadStoreImmediate-1-24"),        (1,"LoadStoreImmediate-1-25"),       (1,"LoadStoreImmediate-1-26"),
  (1,"LoadStoreImmediate-1-27"),        (1,"LoadStoreImmediate-1-28"),       (1,"LoadStoreImmediate-2-1"),
  (1,"LoadStoreImmediate-2-2"),         (1,"LoadStoreImmediate-2-3"),        (1,"LoadStoreImmediate-2-4"),
  (1,"LoadStoreImmediate-2-5"),         (1,"LoadStoreImmediate-2-6"),        (1,"LoadStoreImmediate-2-7"),
  (1,"LoadStoreImmediate-2-8"),         (1,"LoadStoreImmediate-2-9"),        (1,"LoadStoreImmediate-2-10"),
  (1,"LoadStoreImmediate-2-11"),        (1,"LoadStoreImmediate-2-12"),       (1,"LoadStoreImmediate-2-13"),
  (1,"LoadStoreImmediate-2-14"),        (1,"LoadStoreImmediate-2-15"),       (1,"LoadLiteral-1"),
  (1,"LoadLiteral-2"),                  (1,"LoadLiteral-3"),                 (1,"LoadLiteral-4"),
  (1,"LoadStoreRegister-1"),            (1,"LoadStoreRegister-2"),           (1,"LoadStoreRegister-3"),
  (1,"LoadStoreRegister-4"),            (1,"LoadStoreRegister-5"),           (1,"LoadStoreRegister-6"),
  (1,"LoadStoreRegister-7"),            (1,"LoadStoreRegister-8"),           (1,"LoadStoreRegister-9"),
  (1,"LoadStoreRegister-10"),           (1,"LoadStoreRegister-11"),          (1,"LoadStoreRegister-12"),
  (1,"LoadStoreRegister-13"),           (1,"LoadStoreRegister-14"),          (1,"StorePair32-1"),
  (1,"StorePair32-2"),                  (1,"LoadPair32-1"),                  (1,"LoadPair32-2"),
  (1,"LoadStorePair64-1"),              (1,"LoadStorePair64-2"),             (1,"LoadStorePair64-3"),
  (1,"LoadStorePair64-4"),              (1,"NoOperation")]

 fun instClass subs =
     hd (String.tokens  (fn c => Char.compare (c,#"-") = EQUAL) subs);

(* ---------------------------------------------  *)
 type gen = Random.generator
 val rg = Random.newgenseed 1.0
 type init = unit
 val emp_str = ""
     
 fun bits gen bits =
     map (fn x => x = 1) (Random.rangelist (0,2) (bits,gen))

 fun select l =
     let val ln = length l
     in
      fn gen => let val i = Random.range (0,ln) gen in (i,List.nth (l,i)) end
     end

 fun genint gen max =
     Random.range (0,max+1) gen

 fun weighted_select l = select (List.concat (map (fn (n,x) => List.tabulate (n,fn _ => x)) l));
 fun flat xs = List.foldr (fn (x, acc) => x @ acc) [] xs;

 local
     val gen = Random.newgenseed 1.0
     fun random_bit () =
	 if Random.range (0, 2) gen = 1 then boolSyntax.T else boolSyntax.F
 in
 fun random_hex tm =
     let
         val l = Term.free_vars tm
         val s = List.map (fn v => v |-> random_bit ()) l
     in
         bitstringSyntax.hexstring_of_term (Term.subst s tm)
     end
 end

 val random = random_hex o Option.valOf o arm8_stepLib.arm8_pattern;

 fun decomp el =  arm8AssemblerLib.arm8_disassemble [QUOTE el];

 fun inst_decomp inst =
     instructionToString
         (Decode((Option.valOf o BitsN.fromHexString) (inst ,32)))  

 fun member(x,[]) = false
   |  member(x,L) =
      if x=hd(L) then true
      else member(x,tl(L));

 fun intersect([],[]) = []
   | intersect(L1,[]) = []
   | intersect(L1,L2) = if member(hd(L2), L1) then hd(L2)::intersect(L1, tl(L2))
			else intersect(L1, tl(L2));

 fun remChars  (c,s) =
     let fun rem [] = []
           | rem (c'::cs) =
             if c = c'
             then rem cs
             else c'::rem cs
     in
	 implode (rem (explode s)) 
     end

 fun getReg args = 
     map (fn arg => foldl remChars arg [#",", #" ", #"]"]) args


 fun instGen () =
     let val ic = (snd(weighted_select arm8_names_weighted rg))
	 val ib = random ic
	 val wl = filter (fn c => String.isSubstring "WORD" c) (decomp ib)
     in
	 if null wl then (ic, ib) else instGen ()
     end 

 local 
     val gen = Random.newgenseed 1.0
     fun addr_to_hexString adr =
	 (BitsN.toHexString (BitsN.fromInt ((IntInf.fromInt adr), 32)))

     fun cmp_ast s =
	 case instructionFromString s of
	     OK ast =>
	     ast

     fun cmp_mcode ast = 
	 (case Encode ast of
              arm8.ARM8 w =>
              ("",
               Option.SOME(L3.padLeftString(#"0",(8,BitsN.toHexString w))))
            | BadCode err => ("Encode error: " ^ err,NONE));

 in
 fun branch_instGen (pc, base, len) =
     let val adr = base + (4*(Random.range (pc, len) gen))
	 val adr_str = String.concat["bl +#0x", (addr_to_hexString(adr))]
	 val inst = (valOf o snd o cmp_mcode)(cmp_ast adr_str)
     in
	 (emp_str, inst)
     end
 fun c_branch_instGen (inst, pc, base, len) =
     let val adr = base + (4*(Random.range (pc, len) gen))
	 val adr_str = String.concat[hd((p_tokens(hd(decomp(inst)))))," +#0x", (addr_to_hexString(adr))]
	 val inst = (valOf o snd o cmp_mcode)(cmp_ast adr_str)
     in
	 (emp_str, inst)
     end
 end

 fun instsGen (pc, [], base, len)  =
     let val inst = snd (instGen ())
	 val args = getReg (p_tokens ((snd o inst_decomp) inst))
     in
	 (hd args, inst)
     end
     
   | instsGen (pc, src, base, len) =
     let val (c, inst) = instGen ()
	 val args = getReg (p_tokens ((snd o inst_decomp) inst))
	 val inclusion =  intersect (src, tl args)
     in
	 case (instClass c) of 
	     "BranchImmediate" =>  branch_instGen(pc, base, len)
	   | "BranchConditional" => c_branch_instGen (inst,pc, base, len)
	   | _ =>
	     if List.null inclusion
	     then instsGen (pc,src, base, len) 
	     else (hd args, inst)
     end

 (* ---------------------------------------------  *)
 fun progGen (n, base) =
     let val src = ref ([]:string list);
	 val pc = ref 0;
     in
	 (List.tabulate (n, fn _ => let val (d,i) = (instsGen (!pc,!src, base, n)) 			
				    in  (src:= (d::(!src)); pc:= !pc + 1);i end))
     end


 fun bir_prog_gen_arm8 n = map decomp (progGen (n, 0x40000));



end (* local *)

end; (* struct *)

