(* ========================================================================= *)
(* FILE          : bil_valuesScript.sml                                      *)
(* DESCRIPTION   : A model of bil values and types                           *)
(* AUTHOR        : (c) Thomas Tuerk <tuerk@kth.se> based on previous work    *)
(*                 by Roberto Metere, KTH - Royal Institute of Technology    *)
(* DATE          : 2017                                                      *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib;
open wordsTheory bitstringTheory;
open bil_auxiliaryTheory bil_immTheory;

val _ = new_theory "bil_values";

val bil_imm_ss = rewrites ((type_rws ``:bil_imm_t``) @ (type_rws ``:bil_immtype_t``));

(* ------------------------------------------------------------------------- *)
(*  Datatypes                                                                *)
(* ------------------------------------------------------------------------- *)

val _ = Datatype `bil_val_t =
    Unknown
  | Imm bil_imm_t
  | Mem bil_immtype_t (*Addr-Type*) bil_immtype_t (* value-type *) (num -> num)
`;


val _ = Datatype `bil_type_t =
    ImmType bil_immtype_t
  | MemType bil_immtype_t (* Addr-Type *) bil_immtype_t (* Value-Type *)
`;

val BoolType_def = Define `BoolType = ImmType Bit1`;


val bil_val_ss = rewrites (type_rws ``:bil_val_t``);
val bil_type_ss = rewrites (type_rws ``:bil_type_t``);


(* ------------------------------------------------------------------------- *)
(*  Checkers for Values                                                      *)
(* ------------------------------------------------------------------------- *)

val bil_val_is_Unknown_def = Define `bil_val_is_Unknown v = (v = Unknown)`;
val bil_val_is_Imm_def = Define `bil_val_is_Imm v = ?b. (v = Imm b)`;
val bil_val_is_Imm_s_def = Define `bil_val_is_Imm_s s v = ?n. (v = Imm (n2bs n s))`;
val bil_val_is_Bool_def = Define `bil_val_is_Bool = bil_val_is_Imm_s Bit1`;
val bil_val_is_Mem_def = Define `bil_val_is_Mem v = ?at vt mmap. (v = Mem at vt mmap)`;

val bil_val_checker_DEFS = save_thm ("bil_val_checker_DEFS", LIST_CONJ [
  bil_val_is_Unknown_def, bil_val_is_Imm_def, bil_val_is_Imm_s_def,
  bil_val_is_Bool_def, bil_val_is_Mem_def]);


val bil_val_is_Imm_s_ALT_DEF = store_thm ("bil_val_is_Imm_s_ALT_DEF",
``!s v. bil_val_is_Imm_s s v <=>
  (?b. (v = Imm b) /\ (type_of_bil_imm b = s))``,

Cases_on `v` >> (
  SIMP_TAC (std_ss ++ bil_val_ss) [bil_val_is_Imm_s_def,
    type_of_bil_imm_n2bs_INTRO]
));


val bil_val_checker_REWRS = store_thm ("bil_val_checker_REWRS",
  ``bil_val_is_Unknown Unknown /\
    (!b. ~bil_val_is_Unknown (Imm b)) /\
    (!at vt mmap. ~(bil_val_is_Unknown (Mem at vt mmap))) /\

    ~(bil_val_is_Imm Unknown) /\
    (!b. bil_val_is_Imm (Imm b)) /\
    (!at vt mmap. ~(bil_val_is_Imm (Mem at vt mmap))) /\

    ~(bil_val_is_Mem Unknown) /\
    (!b. ~(bil_val_is_Mem (Imm b))) /\
    (!at vt mmap. (bil_val_is_Mem (Mem at vt mmap))) /\

    (!s. ~(bil_val_is_Imm_s s Unknown)) /\
    (!s b. bil_val_is_Imm_s s (Imm b) <=> (type_of_bil_imm b = s)) /\
    (!s at vt mmap. ~(bil_val_is_Imm_s s (Mem at vt mmap))) /\

    (~(bil_val_is_Bool Unknown)) /\
    (!b. bil_val_is_Bool (Imm b) <=> (type_of_bil_imm b = Bit1)) /\
    (!at vt mmap. ~(bil_val_is_Bool (Mem at vt mmap)))``,


  REWRITE_TAC[bil_val_is_Imm_s_ALT_DEF, bil_val_is_Bool_def] >>
  SIMP_TAC (std_ss ++ bil_val_ss) [bil_val_checker_DEFS]);


val bil_val_is_Imm_s_IMPL = store_thm ("bil_val_is_Imm_s_IMPL",
  ``!s v. bil_val_is_Imm_s s v ==> bil_val_is_Imm v``,
SIMP_TAC (std_ss++bil_val_ss) [bil_val_is_Imm_def, bil_val_is_Imm_s_def,
  GSYM LEFT_FORALL_IMP_THM]);

val bil_val_is_Bool_IMPL = store_thm ("bil_val_is_Bool_IMPL",
  ``!v. bil_val_is_Bool v ==> bil_val_is_Imm v``,
SIMP_TAC (std_ss++bil_val_ss) [bil_val_is_Imm_def, bil_val_is_Bool_def,
  bil_val_is_Imm_s_def, GSYM LEFT_FORALL_IMP_THM]);



(* ------------------------------------------------------------------------- *)
(*  Some basic typing                                                        *)
(* ------------------------------------------------------------------------- *)

val type_of_bil_val_def = Define `
  (type_of_bil_val Unknown = NONE) /\
  (type_of_bil_val (Imm imm) = SOME (ImmType (type_of_bil_imm imm))) /\
  (type_of_bil_val (Mem at vt _) = SOME (MemType at vt))`;

val bil_type_is_ImmType_def = Define `bil_type_is_ImmType ty = (?s. ty = ImmType s)`;
val bil_type_is_ImmType_s_def = Define `bil_type_is_ImmType_s s ty = (ty = ImmType s)`
val bil_type_is_BoolType_def = Define `bil_type_is_BoolType ty = (ty = ImmType Bit1)`
val bil_type_is_MemType_def = Define `bil_type_is_MemType ty = (?at vt. ty = MemType at vt)`;

val bil_type_checker_DEFS = save_thm ("bil_type_checker_DEFS", LIST_CONJ [
  bil_type_is_ImmType_def, bil_type_is_ImmType_s_def,
  bil_type_is_BoolType_def, bil_type_is_MemType_def]);


val bil_type_checker_REWRS = store_thm ("bil_type_checker_REWRS", ``
    (!b. bil_type_is_ImmType (ImmType b)) /\
    (!at vt. ~(bil_type_is_ImmType (MemType at vt))) /\

    (!b. ~(bil_type_is_MemType (ImmType b))) /\
    (!at vt. (bil_type_is_MemType (MemType at vt))) /\

    (!s b. bil_type_is_ImmType_s s (ImmType b) <=> (b = s)) /\
    (!s at vt. ~(bil_type_is_ImmType_s s (MemType at vt))) /\

    (!b. bil_type_is_BoolType (ImmType b) <=> (b = Bit1)) /\
    (!at vt. ~(bil_type_is_BoolType (MemType at vt)))``,

  SIMP_TAC (std_ss ++ bil_type_ss) [bil_type_checker_DEFS]);


val bil_type_is_ImmType_s_IMPL = store_thm ("bil_type_is_ImmType_s_IMPL",
  ``!s v. bil_type_is_ImmType_s s v ==> bil_type_is_ImmType v``,
SIMP_TAC (std_ss++bil_type_ss) [bil_type_is_ImmType_def, bil_type_is_ImmType_s_def]);


val bil_type_is_BoolType_IMPL = store_thm ("bil_type_is_BoolType_IMPL",
  ``!v. bil_type_is_BoolType v ==> bil_type_is_ImmType v``,
SIMP_TAC (std_ss++bil_type_ss) [bil_type_is_ImmType_def, bil_type_is_BoolType_def]);


val type_of_bil_val_EQ_ELIMS = store_thm ("type_of_bil_val_EQ_ELIMS",
  ``(!v. (type_of_bil_val v = NONE) <=> (v = Unknown)) /\
    (!v ty. (type_of_bil_val v = SOME (ImmType ty)) <=>
            (?i. (type_of_bil_imm i = ty) /\ (v = Imm i))) /\
    (!v aty vty. (type_of_bil_val v = SOME (MemType aty vty)) <=>
            (?f. (v = Mem aty vty f)))``,
REPEAT CONJ_TAC >> Cases >> (
  SIMP_TAC (std_ss++bil_val_ss++bil_type_ss) [type_of_bil_val_def]
));


val _ = export_theory();
