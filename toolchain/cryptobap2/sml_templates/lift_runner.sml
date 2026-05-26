open HolKernel Parse
open PPBackEnd;
open bir_update_blockTheory;
open bir_inst_liftingTheory;

open bir_inst_liftingLib;
open bir_inst_liftingHelpersLib;
open bir_lifter_simple_interfaceLib;
open gcc_supportLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;

val _ = new_theory $theory;

val arch_str = $arch;
val dafilename = $dafilename;
val symbs_sec_text = [
$symbol_lines
  ];
val selected_sections = [
$section_lines
  ];
val lift_all_symbols = $lift_all_symbols;

fun list_has value items = List.exists (fn x => x = value) items;

val symb_filter_lift = fn secname =>
  if list_has "*" selected_sections orelse list_has secname selected_sections
  then (fn symbname => lift_all_symbols orelse list_has symbname symbs_sec_text)
  else (K false);

val (region_map, sections) = read_disassembly_file_regions_filter symb_filter_lift dafilename;
val prog_range = da_sections_minmax sections;
val (thm, errors) = $lifter prog_range sections;
val _ = save_thm ($theorem_name, thm);
val _ =
  let
    val (_, _, _, prog_tm) = (dest_bir_is_lifted_prog o concl) thm;
    val out_stream = TextIO.openOut $label_dump;
  in
    (TextIO.output (out_stream, term_to_string prog_tm); TextIO.closeOut out_stream)
  end;
val _ = export_theory();
