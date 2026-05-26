open HolKernel Parse

open ${theory}Theory;
open yamlLib;
open pipelineConfigLib;
open bir_envSyntax;
open bir_symbexec_stateLib;
open bir_symbexec_coreLib;
open bir_symbexec_compLib;
open bir_symbexec_stepLib;
open bir_symbexec_sumLib;
open bir_block_collectionLib;
open bir_programSyntax;
open bir_valuesSyntax;
open bir_immSyntax;
open bir_expSyntax;
open bir_exp_immSyntax;
open bir_exec_typingLib;
open bir_inst_liftingHelpersLib;
open HolBACoreSimps;
open HolBASimps;
open bslSyntax;
open bir_smtLib;
open bir_exp_to_wordsLib;
open Z3_SAT_modelLib;
open bir_exp_substitutionsSyntax;
open binariesLib;
open bir_auxiliaryLib;
open bir_constpropLib;
val _ = pipelineConfigLib.load_config $pipeline_yaml;
open commonBalrobScriptLib;
open bir_cfgLib;
open Redblackmap;
open bir_symbexec_oracleLib;
open sbir_treeLib;
open sapicplusTheory;
open sapicplusSyntax;
open translate_to_sapicTheory;
open rich_listTheory;
open translate_to_sapicLib;
open messagesTheory;
open messagesSyntax;
open tree_to_processLib;
open sapic_to_fileLib;
open CryptoBAP2Pipeline;

val _ = new_theory $runner_theory;

val (_, _, _, prog_tm) =
  (dest_bir_is_lifted_prog o concl) (DB.fetch $theory_db $theorem_name);
val bl_dict_ = gen_block_dict prog_tm;
val prog_lbl_tms_ = get_block_dict_keys bl_dict_;
val _ = binariesLib.set_prog_lbl_tms prog_lbl_tms_;
val prog_vars_base = gen_vars_of_prog prog_tm;
val prog_vars = $prog_vars;
val n_dict = bir_cfgLib.cfg_build_node_dict bl_dict_ prog_lbl_tms_;
val adr_dict = bir_symbexec_PreprocessLib.fun_addresses_dict bl_dict_ prog_lbl_tms_;

val binary_model_schema = $binary_model_schema;
val case_metadata_json = $case_metadata_json;
val provenance_json = $provenance_json;
val proof_status_json = $proof_status_json;

fun term_name tm =
  (fst (bir_envSyntax.dest_BVar_string tm)) handle _ => term_to_string tm;

fun state_status_json syst =
  json_string (term_to_string (SYST_get_status syst));

fun path_predicates_json preds =
  json_list (List.map (fn pred => json_string (term_name pred)) preds);

fun symbolic_value_json (bv, symbv) =
  json_object [
    ("name", json_string (term_name bv)),
    ("term", json_string (term_to_string bv)),
    ("value", json_string (symbv_to_string symbv))
  ];

type fragment_spec = {
  name : string,
  entry_label_text : string,
  exit_label_texts : string list,
  lbl_tm : term,
  stop_lbl_tms : term list,
  start_label : IntInf.int,
  end_label : IntInf.int option
};

val fragment_specs : fragment_spec list = $fragment_specs;

val _ = set_stub_unclassified_calls (pipelineConfigLib.get_stub_unclassified_calls ());
val _ = set_allow_unmapped_memory_overapprox (pipelineConfigLib.get_allow_unmapped_memory_overapprox ());

fun configure_fragment_range (spec : fragment_spec) =
  case #end_label spec of
      SOME stop_label => set_active_fragment_range (#start_label spec, stop_label)
    | NONE => clear_active_fragment_range ();

fun run_fragment (spec : fragment_spec) =
  let
    val _ = configure_fragment_range spec;
    val lbl_tm = #lbl_tm spec;
    val stop_lbl_tms = #stop_lbl_tms spec;
    val syst = init_state lbl_tm prog_vars;
    val syst = state_add_preds "init_pred" [``bir_exp_true``] syst;
    val systs = symb_exec_to_stop (abpfun false) n_dict bl_dict_ [syst] stop_lbl_tms adr_dict [];
    val (systs_noassertfailed, _) =
      List.partition (fn syst => not (identical (SYST_get_status syst) BST_AssertionViolated_tm)) systs;
    val predlists = List.map (fn syst => ((rev o SYST_get_pred) syst)) systs_noassertfailed;
    val predlists_refined = List.map (fn lst => bir_symbexec_sortLib.removeDuplicates lst) predlists;
    val tree = predlist_to_tree predlists_refined;
    val vals_list = bir_symbexec_treeLib.symb_execs_vals_term systs_noassertfailed [];
    val sort_vals = bir_symbexec_sortLib.refine_symb_val_list vals_list;
    val valtr = tree_with_value tree sort_vals;
    val sapic_process = sbir_tree_sapic_process sort_vals (purge_tree valtr);
    val refined_process = refine_process sapic_process;
    val sapic_text = process_to_string refined_process;
    val model_json =
      json_object [
        ("name", json_string (#name spec)),
        ("entry_label", #entry_label_text spec),
        ("exit_labels", json_list (#exit_label_texts spec)),
        ("total_states", json_int (List.length systs)),
        ("assertion_clean_states", json_int (List.length systs_noassertfailed)),
        ("final_statuses", json_list (List.map state_status_json systs)),
        ("path_predicates", json_list (List.map path_predicates_json predlists_refined)),
        ("symbolic_values", json_list (List.map symbolic_value_json sort_vals)),
        ("sapic", json_string sapic_text)
      ];
  in
    (#name spec, sapic_text, model_json)
  end;

fun append_text (path, content) =
  let
    val out_stream = TextIO.openAppend path;
  in
    (TextIO.output (out_stream, content); TextIO.closeOut out_stream)
  end;

fun is_empty_sapic_process text =
  text = "0";

val model_prefix =
  "{" ^ String.concatWith "," [
    json_field ("schema", json_string binary_model_schema),
    json_field ("case", case_metadata_json),
    json_field ("provenance", provenance_json),
    json_field ("proof_status", proof_status_json)
  ] ^ "," ^ json_string "fragments" ^ ":[";

fun write_fragment_outputs [] _ _ = ()
  | write_fragment_outputs (spec :: rest) sapic_first model_first =
      let
        val (_, sapic_text, model_json) = run_fragment spec;
        val emit_sapic = not (is_empty_sapic_process sapic_text);
        val sapic_prefix = if sapic_first then "" else "\n\n";
        val model_prefix = if model_first then "" else ",";
        val next_sapic_first = if emit_sapic then false else sapic_first;
      in
        if emit_sapic then
          append_text ($sapic_output, sapic_prefix ^ sapic_text)
        else
          ();
        append_text ($model_output, model_prefix ^ model_json);
        write_fragment_outputs rest next_sapic_first false
      end;

val _ = write_sapic_text ($sapic_output, "");
val _ = write_binary_model_text ($model_output, model_prefix);
val _ = write_fragment_outputs fragment_specs true true;
val _ = append_text ($model_output, "]}\n");
val _ = export_theory();
