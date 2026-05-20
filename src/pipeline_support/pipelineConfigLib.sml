val _ =
  let
    fun first_env [] = NONE
      | first_env (name :: rest) =
          (case OS.Process.getEnv name of
             SOME path => SOME path
           | NONE => first_env rest);
    fun holba_dirs root =
      List.map
        (fn suffix => root ^ suffix)
        ["/src/extra",
         "/src/theory/bir",
         "/src/theory/bir-support",
         "/src/shared",
         "/src/shared/convs",
         "/src/shared/smt",
         "/src/tools/cfg",
         "/src/tools/exec",
         "/src/tools/lifter",
         "/src/tools/symbexec"];
  in
    case first_env ["HOLBADIR", "HOLBA_DIR"] of
      SOME root => loadPath := holba_dirs root @ (!loadPath)
    | NONE => ()
  end;

val _ =
  List.app load
    ["HolBACoreSimps",
     "HolBASimps",
     "bir_exp_substitutionsSyntax",
     "bir_programSyntax",
     "bir_valuesSyntax",
     "bir_immSyntax",
     "bir_expSyntax",
     "bir_exp_immSyntax",
     "bir_envSyntax",
     "bir_bool_expSyntax",
     "bir_program_labelsSyntax",
     "bir_typing_expSyntax",
     "bir_block_collectionLib",
     "bir_cfgLib",
     "bir_exec_typingLib",
     "bir_exp_typecheckLib",
     "bslSyntax",
     "bir_exp_to_wordsLib",
     "bir_smtLib",
     "Z3_SAT_modelLib"];

(*
 * pipelineConfigLib.sml — Typed accessors for the unified pipeline.yaml
 *
 * Call  pipelineConfigLib.load_config "pipeline.yaml"  once at startup.
 * All other modules query configuration through the accessor functions
 * exported by this structure, eliminating direct file I/O in oracleLib,
 * funcLib and treeLib.
 *)

structure pipelineConfigLib =
struct

(* ------------------------------------------------------------------ *)
(*  Internal state                                                     *)
(* ------------------------------------------------------------------ *)

val cfg : yamlLib.yaml ref = ref yamlLib.YNull;

fun require_loaded () =
  case !cfg of
      yamlLib.YNull => raise Fail "pipelineConfigLib: config not loaded -- call load_config first"
    | y => y;

(* ------------------------------------------------------------------ *)
(*  Load                                                               *)
(* ------------------------------------------------------------------ *)

fun load_config (path : string) : unit =
  let
    val fullpath = OS.Path.mkAbsolute
                     { path = path
                     , relativeTo = OS.FileSys.getDir () }
    val y = yamlLib.parse_file fullpath
  in
    cfg := y
  end;

(* ------------------------------------------------------------------ *)
(*  Pipeline section                                                   *)
(* ------------------------------------------------------------------ *)

fun pipeline_section () =
  yamlLib.lookupExn (require_loaded ()) "pipeline";

fun get_theory_name () : string =
  yamlLib.toString (yamlLib.lookupExn (pipeline_section ()) "theory");

fun get_entry_label () : int =
  yamlLib.toInt (yamlLib.lookupExn (pipeline_section ()) "entry_label");

fun get_exit_labels () : int list =
  yamlLib.toIntList (yamlLib.lookupExn (pipeline_section ()) "exit_labels");

fun get_output_file () : string =
  yamlLib.toString (yamlLib.lookupExn (pipeline_section ()) "output_file");

fun get_stub_unclassified_calls () : bool =
  case yamlLib.lookup (pipeline_section ()) "stub_unclassified_calls" of
      NONE => false
    | SOME yaml => yamlLib.toBool yaml;

fun get_allow_unmapped_memory_overapprox () : bool =
  case yamlLib.lookup (pipeline_section ()) "allow_unmapped_memory_overapprox" of
      NONE => false
    | SOME yaml => yamlLib.toBool yaml;

(* Extra variables: list of {name, type, width} records *)
type var_spec = { name : string, typ : string, width : int };

fun parse_var_spec (yamlLib.YMapping pairs) : var_spec =
      { name  = yamlLib.toString (yamlLib.lookupExn (yamlLib.YMapping pairs) "name")
      , typ   = yamlLib.toString (yamlLib.lookupExn (yamlLib.YMapping pairs) "type")
      , width = yamlLib.toInt    (yamlLib.lookupExn (yamlLib.YMapping pairs) "width")
      }
  | parse_var_spec _ = raise Fail "pipelineConfigLib: extra_variable entry must be a mapping";

fun get_extra_variables () : var_spec list =
  case yamlLib.lookup (pipeline_section ()) "extra_variables" of
      NONE                    => []
    | SOME (yamlLib.YNull)    => []
    | SOME (yamlLib.YSequence items) =>
        List.map parse_var_spec items
    | SOME _ => raise Fail "pipelineConfigLib: extra_variables must be a sequence";

(* Fragment specs: list of {name, entry_label, optional end_label, exit_labels} records *)
type fragment_spec = { name : string, entry_label : int, end_label : int option, exit_labels : int list };

fun parse_fragment_spec (yamlLib.YMapping pairs) : fragment_spec =
      let
        val item = yamlLib.YMapping pairs;
        val end_label =
          case yamlLib.lookup item "end_label" of
              NONE => NONE
            | SOME yaml => SOME (yamlLib.toInt yaml);
      in
        { name = yamlLib.toString (yamlLib.lookupExn item "name")
        , entry_label = yamlLib.toInt (yamlLib.lookupExn item "entry_label")
        , end_label = end_label
        , exit_labels = yamlLib.toIntList (yamlLib.lookupExn item "exit_labels")
        }
      end
  | parse_fragment_spec _ = raise Fail "pipelineConfigLib: fragment entry must be a mapping";

fun get_fragment_specs () : fragment_spec list =
  case yamlLib.lookup (pipeline_section ()) "fragments" of
      NONE => []
    | SOME (yamlLib.YNull) => []
    | SOME (yamlLib.YSequence items) => List.map parse_fragment_spec items
    | SOME _ => raise Fail "pipelineConfigLib: fragments must be a sequence";

(* ------------------------------------------------------------------ *)
(*  Functions section                                                  *)
(* ------------------------------------------------------------------ *)

fun functions_section () =
  yamlLib.lookupExn (require_loaded ()) "functions";

fun get_library_functions () : string list =
  yamlLib.toStringList (yamlLib.lookupExn (functions_section ()) "library");

fun get_adversary_functions () : string list =
  yamlLib.toStringList (yamlLib.lookupExn (functions_section ()) "adversary");

(* ------------------------------------------------------------------ *)
(*  Cryptographic functions section  (name → operation label)          *)
(* ------------------------------------------------------------------ *)

fun get_crypto_function_map () : (string * string) list =
  yamlLib.toStringMap (yamlLib.lookupExn (require_loaded ()) "cryptographic_functions");

fun get_crypto_callsite_map () : (string * string) list =
  case yamlLib.lookup (require_loaded ()) "cryptographic_callsite_labels" of
      NONE                 => []
    | SOME yamlLib.YNull   => []
    | SOME node            => yamlLib.toStringMap node;

(* Look up operation label for a given binary function name.
   Returns the label string or "C_Lib" if not found. *)
fun crypto_label_of (fun_name : string) : string =
  case List.find (fn (k, _) => k = fun_name) (get_crypto_function_map ()) of
      SOME (_, lbl) => lbl
    | NONE          => "C_Lib";

fun crypto_callsite_label_of (label : IntInf.int) : string option =
  case List.find (fn (k, _) => k = IntInf.toString label) (get_crypto_callsite_map ()) of
      SOME (_, lbl) => SOME lbl
    | NONE          => NONE;

(* ------------------------------------------------------------------ *)
(*  Arities section                                                    *)
(* ------------------------------------------------------------------ *)

fun arities_section () =
  yamlLib.lookupExn (require_loaded ()) "arities";

fun get_library_arity () : IntInf.int =
  IntInf.fromInt (yamlLib.toInt (yamlLib.lookupExn (arities_section ()) "library"));

fun get_adversary_arity () : IntInf.int =
  IntInf.fromInt (yamlLib.toInt (yamlLib.lookupExn (arities_section ()) "adversary"));

(* ------------------------------------------------------------------ *)
(*  Events section                                                     *)
(* ------------------------------------------------------------------ *)

fun get_event_names () : string list =
  case yamlLib.lookup (require_loaded ()) "events" of
      NONE                     => []
    | SOME (yamlLib.YNull)     => []
    | SOME (yamlLib.YSequence items) => List.map yamlLib.toString items
    | SOME (yamlLib.YString s) => [s]
    | SOME _ => raise Fail "pipelineConfigLib: events must be a sequence";

end (* structure pipelineConfigLib *)
