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
 * yamlLib.sml — Minimal YAML-subset parser for SML (Standard ML)
 *
 * Supports:
 *   - Block mappings        (key: value, key:\n  nested)
 *   - Block sequences       (- item)
 *   - Scalars: unquoted strings, double-quoted strings, integers
 *   - Inline empty sequence ([] on the same line as a key)
 *   - Comments              (# ...)
 *   - Blank lines
 *
 * Does NOT support:
 *   - Flow-style mappings {k: v}
 *   - Anchors / aliases
 *   - Multi-line scalars (|, >)
 *   - Tags (!!)
 *   - Multiple documents (---, ...)
 *
 * Usage:
 *   val yaml = yamlLib.parse_file "pipeline.yaml";
 *   val th   = yamlLib.lookup yaml "pipeline";
 *   val name = yamlLib.lookup (valOf th) "theory";
 *   val s    = yamlLib.toString (valOf name);  (* "XORexample" *)
 *)

structure yamlLib =
struct

(* ------------------------------------------------------------------ *)
(*  Datatype                                                           *)
(* ------------------------------------------------------------------ *)

datatype yaml = YMapping of (string * yaml) list
              | YSequence of yaml list
              | YString  of string
              | YInt     of int
              | YNull

(* ------------------------------------------------------------------ *)
(*  Helpers                                                            *)
(* ------------------------------------------------------------------ *)

(* Count leading spaces — tabs are not supported *)
fun indent_of s =
  let fun go (i, []) = i
        | go (i, #" " :: rest) = go (i + 1, rest)
        | go (i, _) = i
  in go (0, explode s) end;

fun strip_leading_spaces s =
  String.extract (s, indent_of s, NONE);

(* Remove trailing \r\n or \n and trailing whitespace *)
fun trim_right s =
  implode (rev (List.filter (fn c => c <> #"\r")
    (let fun drop [] = []
           | drop (c :: cs) = if Char.isSpace c then drop cs
                              else c :: cs
     in drop (rev (explode s)) end)));

fun trim s = strip_leading_spaces (trim_right s);

(* Strip inline comment: everything after an unquoted # *)
fun strip_comment s =
  let
    fun go ([], acc) = rev acc
      | go (cs, acc) =
          case cs of
            [] => rev acc
          | #"#" :: _ => rev acc
          | #"\"" :: rest =>
              (* skip inside quotes *)
              let fun skip_q ([], a) = rev a
                    | skip_q (#"\"" :: r, a) = go (r, #"\"" :: a)
                    | skip_q (#"\\" :: c :: r, a) = skip_q (r, c :: #"\\" :: a)
                    | skip_q (c :: r, a) = skip_q (r, c :: a)
              in skip_q (rest, #"\"" :: acc) end
          | c :: rest => go (rest, c :: acc)
  in implode (go (explode s, [])) end;

fun find_unquoted_colon s =
  let
    val size = String.size s;
    fun go i in_quote escaped =
      if i >= size then NONE
      else
        let val c = String.sub (s, i) in
          if escaped then go (i + 1) in_quote false
          else if in_quote andalso c = #"\\" then go (i + 1) true true
          else if c = #"\"" then go (i + 1) (not in_quote) false
          else if c = #":" andalso not in_quote then SOME i
          else go (i + 1) in_quote false
        end
  in go 0 false false end;

fun has_unquoted_colon s =
  case find_unquoted_colon s of
      SOME _ => true
    | NONE => false;

fun unescape_double_quoted s =
  let
    fun go [] acc = implode (rev acc)
      | go (#"\\" :: #"\"" :: rest) acc = go rest (#"\"" :: acc)
      | go (#"\\" :: #"\\" :: rest) acc = go rest (#"\\" :: acc)
      | go (#"\\" :: #"n" :: rest) acc = go rest (#"\n" :: acc)
      | go (#"\\" :: #"r" :: rest) acc = go rest (#"\r" :: acc)
      | go (#"\\" :: #"t" :: rest) acc = go rest (#"\t" :: acc)
      | go (#"\\" :: c :: rest) acc = go rest (c :: acc)
      | go (c :: rest) acc = go rest (c :: acc)
  in go (explode s) [] end;

fun is_double_quoted s =
  String.size s >= 2
  andalso String.isPrefix "\"" s
  andalso String.sub (s, String.size s - 1) = #"\"";

(* Parse a scalar value from a trimmed string *)
fun parse_scalar s =
  let val s' = trim s in
    if s' = "" orelse s' = "~" orelse s' = "null"
    then YNull
    else if is_double_quoted s'
    then (* double-quoted string *)
      let val inner = String.substring (s', 1, String.size s' - 2)
      in YString (unescape_double_quoted inner) end
    else (* try integer, otherwise string *)
      case Int.fromString s' of
          SOME n => YInt n
        | NONE   => YString s'
  end;

fun parse_key s =
  case parse_scalar s of
      YString key => key
    | YInt n => Int.toString n
    | YNull => ""
    | _ => trim s;

(* Check if trimmed string is "[]" (inline empty sequence) *)
fun is_empty_seq s = (trim s = "[]");

(* ------------------------------------------------------------------ *)
(*  Tokenised lines                                                    *)
(* ------------------------------------------------------------------ *)

(* Each source line is classified after stripping comments *)
datatype line_kind =
    LBlank
  | LMappingEntry of { indent: int, key: string, rest: string }
                      (* rest is the part after ": ", may be "" *)
  | LSequenceItem of { indent: int, rest: string }
                      (* rest is the part after "- " *)

fun classify_line raw =
  let
    val s0 = strip_comment raw
    val s  = trim_right s0    (* keep leading spaces, drop trailing *)
  in
    if trim s = "" then LBlank
    else
      let val ind = indent_of s
          val body = strip_leading_spaces s
      in
        if String.isPrefix "- " body orelse body = "-"
        then
          let val rest = if body = "-" then ""
                         else String.extract (body, 2, NONE)
          in LSequenceItem { indent = ind, rest = rest } end
        else
          (* look for "key:" or "key: value" *)
          case find_unquoted_colon body of
              NONE => LMappingEntry { indent = ind, key = parse_key body, rest = "" }
            | SOME i =>
                let val key = parse_key (String.substring (body, 0, i))
                    val after_colon = String.extract (body, i + 1, NONE)
                    val rest = strip_leading_spaces after_colon
                in LMappingEntry { indent = ind, key = key, rest = rest } end
      end
  end;

(* ------------------------------------------------------------------ *)
(*  Recursive-descent parser on classified lines                       *)
(* ------------------------------------------------------------------ *)

(* Lines is a (lineNo * line_kind) list ref used as a mutable stream *)
type parse_state = (int * line_kind) list ref

fun peek (ps : parse_state) =
  case !ps of [] => NONE | (x :: _) => SOME x;

fun advance (ps : parse_state) =
  case !ps of [] => () | (_ :: rest) => ps := rest;

fun skip_blanks (ps : parse_state) =
  case !ps of
      (_, LBlank) :: rest => (ps := rest; skip_blanks ps)
    | _ => ();

(* current_indent: indentation required for items at this nesting *)
(* parse_block returns a yaml value at the given indent level *)

fun parse_block (ps : parse_state) (min_indent : int) : yaml =
  let val _ = skip_blanks ps
  in
    case peek ps of
        NONE => YNull
      | SOME (_, LBlank) => YNull (* shouldn't happen after skip *)
      | SOME (_, LSequenceItem { indent, ... }) =>
          if indent >= min_indent then parse_sequence ps indent
          else YNull
      | SOME (_, LMappingEntry { indent, key, rest }) =>
          if indent >= min_indent then parse_mapping ps indent
          else YNull
  end

and parse_mapping (ps : parse_state) (base_indent : int) : yaml =
  let
    fun collect acc =
      let val _ = skip_blanks ps in
        case peek ps of
            NONE => YMapping (rev acc)
          | SOME (_, LMappingEntry { indent, key, rest }) =>
              if indent = base_indent then
                let val _ = advance ps
                    val value =
                      if is_empty_seq rest then YSequence []
                      else if rest <> ""
                      then
                        (* check if rest is itself "- item" for inline seq *)
                        parse_scalar rest
                      else
                        (* value is indented block on next lines *)
                        parse_block ps (base_indent + 1)
                in collect ((key, value) :: acc) end
              else if indent > base_indent then
                (* shouldn't normally happen — treat as end *)
                YMapping (rev acc)
              else
                YMapping (rev acc)
          | SOME (_, LSequenceItem { indent, ... }) =>
              if indent > base_indent then
                (* a sequence as the value of the LAST key — but we
                   already advanced past the key line. This means the
                   sequence is a child block. We'll handle it via
                   parse_block in the value branch above. *)
                YMapping (rev acc)
              else
                YMapping (rev acc)
          | _ => YMapping (rev acc)
      end
  in collect [] end

and parse_sequence (ps : parse_state) (base_indent : int) : yaml =
  let
    fun collect acc =
      let val _ = skip_blanks ps in
        case peek ps of
            NONE => YSequence (rev acc)
          | SOME (_, LSequenceItem { indent, rest }) =>
              if indent = base_indent then
                let val _ = advance ps
                    val item =
                      if rest = "" then
                        (* nested block under this "- " *)
                        parse_block ps (indent + 2)
                      else
                        (* Does rest contain a colon?  If not, it's a scalar. *)
                        if not (has_unquoted_colon rest)
                        then parse_scalar rest
                        else
                        (* check if it looks like a mapping "key: val" *)
                        let val cls = classify_line (rest) in
                          case cls of
                              LMappingEntry { key, rest = r, ... } =>
                                if r <> ""
                                then
                                  (* single-line mapping entry inside seq, e.g. "- name: key" *)
                                  (* but there might be more entries at deeper indent *)
                                  let
                                    val first_val = if is_empty_seq r then YSequence []
                                                    else parse_scalar r
                                    val first_pair = (key, first_val)
                                    (* check for continuation entries at indent + 2 *)
                                    val _ = skip_blanks ps
                                    val more = case peek ps of
                                        SOME (_, LMappingEntry { indent = ni, ... }) =>
                                          if ni > indent then
                                            case parse_mapping ps ni of
                                                YMapping pairs => pairs
                                              | _ => []
                                          else []
                                      | _ => []
                                  in YMapping (first_pair :: more) end
                                else
                                  (* "- key:" with value on next lines *)
                                  let val child_val = parse_block ps (indent + 2)
                                  in YMapping [(key, child_val)] end
                            | _ => parse_scalar rest
                        end
                in collect (item :: acc) end
              else
                YSequence (rev acc)
          | _ => YSequence (rev acc)
      end
  in collect [] end;

(* ------------------------------------------------------------------ *)
(*  Top-level parse                                                    *)
(* ------------------------------------------------------------------ *)

fun parse (text : string) : yaml =
  let
    val raw_lines = String.fields (fn c => c = #"\n") text
    val classified = List.map classify_line raw_lines
    val numbered   = let fun num (_, []) = []
                           | num (i, x :: xs) = (i, x) :: num (i+1, xs)
                     in num (1, classified) end
    (* remove blank lines at end *)
    val ps : parse_state = ref numbered
  in
    parse_block ps 0
  end;

fun parse_file (path : string) : yaml =
  let
    val ins  = TextIO.openIn path
    val text = TextIO.inputAll ins
    val _    = TextIO.closeIn ins
  in
    parse text
  end;

(* ------------------------------------------------------------------ *)
(*  Accessor helpers                                                   *)
(* ------------------------------------------------------------------ *)

fun lookup (YMapping pairs) (key : string) : yaml option =
      (case List.find (fn (k, _) => k = key) pairs of
           SOME (_, v) => SOME v
         | NONE => NONE)
  | lookup _ _ = NONE;

fun lookupExn y key =
  case lookup y key of
      SOME v => v
    | NONE   => raise Fail ("yamlLib: key not found: " ^ key);

fun toString (YString s) = s
  | toString (YInt n)    = Int.toString n
  | toString _           = raise Fail "yamlLib.toString: not a scalar";

fun toInt (YInt n)    = n
  | toInt (YString s) = (case Int.fromString s of
                            SOME n => n
                          | NONE => raise Fail ("yamlLib.toInt: not an integer: " ^ s))
  | toInt _           = raise Fail "yamlLib.toInt: not an integer";

fun toBool (YString s) =
      if s = "true" then true
      else if s = "false" then false
      else raise Fail ("yamlLib.toBool: not a boolean: " ^ s)
  | toBool _ = raise Fail "yamlLib.toBool: not a boolean";

fun toStringList (YSequence items) = List.map toString items
  | toStringList (YNull)           = []
  | toStringList (YString "[]")    = []
  | toStringList _                 = raise Fail "yamlLib.toStringList: not a sequence";

fun toIntList (YSequence items) = List.map toInt items
  | toIntList (YNull)           = []
  | toIntList (YString "[]")    = []
  | toIntList _                 = raise Fail "yamlLib.toIntList: not a sequence";

fun toStringMap (YMapping pairs) =
      List.map (fn (k, v) => (k, toString v)) pairs
  | toStringMap (YNull) = []
  | toStringMap (YString "{}") = []
  | toStringMap _ = raise Fail "yamlLib.toStringMap: not a mapping";

fun toMappingList (YSequence items) =
      List.map (fn (YMapping pairs) => pairs
                 | _ => raise Fail "yamlLib.toMappingList: item not a mapping") items
  | toMappingList (YNull) = []
  | toMappingList _ = raise Fail "yamlLib.toMappingList: not a sequence";

(* Pretty-print for debugging *)
fun pp (yaml : yaml) : string =
  let
    fun go indent (YNull) = "(null)"
      | go indent (YString s) = "\"" ^ s ^ "\""
      | go indent (YInt n) = Int.toString n
      | go indent (YSequence items) =
          let val pad = CharVector.tabulate (indent, fn _ => #" ")
          in "[\n" ^ String.concat
               (List.map (fn item => pad ^ "  - " ^ go (indent+2) item ^ "\n") items)
             ^ pad ^ "]" end
      | go indent (YMapping pairs) =
          let val pad = CharVector.tabulate (indent, fn _ => #" ")
          in "{\n" ^ String.concat
               (List.map (fn (k,v) => pad ^ "  " ^ k ^ ": " ^ go (indent+2) v ^ "\n") pairs)
             ^ pad ^ "}" end
  in go 0 yaml end;

end (* structure yamlLib *)
