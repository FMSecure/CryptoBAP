structure CryptoBAP2Pipeline =
struct

fun write_text (path, content) =
    sapic_to_fileLib.write_sapic_to_file_path path content;

fun write_sapic_text (path, content) =
    write_text (path, content);

fun write_binary_model_text (path, content) =
    write_text (path, content);

fun json_escape text =
    let
        fun escape_char #"\"" = "\\\""
          | escape_char #"\\" = "\\\\"
          | escape_char #"\n" = "\\n"
          | escape_char #"\r" = "\\r"
          | escape_char #"\t" = "\\t"
          | escape_char ch = String.str ch;
    in
        String.concat (List.map escape_char (String.explode text))
    end;

fun json_string text =
    "\"" ^ json_escape text ^ "\"";

fun json_int value =
    Int.toString value;

fun json_list values =
    "[" ^ String.concatWith "," values ^ "]";

fun json_field (name, value) =
    json_string name ^ ":" ^ value;

fun json_object fields =
    "{" ^ String.concatWith "," (List.map json_field fields) ^ "}";

fun sapic_process_to_text process =
    sapic_to_fileLib.process_to_string process;

fun refined_process_to_text process =
    sapic_process_to_text (sapic_to_fileLib.refine_process process);

fun write_process (path, process) =
    write_sapic_text (path, sapic_process_to_text process);

fun write_refined_process (path, process) =
    write_sapic_text (path, refined_process_to_text process);

end
