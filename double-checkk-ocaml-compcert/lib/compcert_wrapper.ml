(* filepath: c:\Users\tonst\OneDrive\Desktop\Dev\double-checkk\double-checkk-ocaml-compcert\lib\compcert_wrapper.ml *)
(* Helper: read a whole file into a string *)
let slurp_file (path : string) : string =
  let ic = open_in path in
  let len = in_channel_length ic in
  let s = really_input_string ic len in
  close_in ic;
  s

(* Wrap a snippet so it becomes a valid C translation unit.
   - If you pass a statement/expression, it’s wrapped into a stub function.
   - If you pass a full translation unit, set ~is_full=true to bypass wrapping. *)
let wrap_snippet ~(is_full: bool) (src : string) : string =
  if is_full then src
  else
    (* Minimal wrapper. You can add includes or prototypes if needed. *)
    "int __doublecheckk_entry(void) {\n" ^
    src ^
    (if String.length src > 0 && src.[String.length src - 1] = ';' then "\n" else ";\n") ^
    "return 0;\n}\n"

type verify_result = {
  ok : bool;            (* Did clightgen exit with 0? *)
  clight_v : string option;  (* The generated Coq (.v) text, if any *)
  v_path : string option;    (* Path to the generated .v file *)
  cmd : string;         (* Command we executed *)
}

let clight_of_source ?(is_full=false) (src : string) : verify_result =
  (* Write to a temp .c file in the system temp dir *)
  let c_path = Filename.temp_file "doublecheckk" ".c" in
  let oc = open_out c_path in
  output_string oc (wrap_snippet ~is_full src);
  close_out oc;

  (* clightgen writes <basename>.v next to the input *)
  let v_path = (Filename.chop_extension c_path) ^ ".v" in
  let cmd = Printf.sprintf "clightgen -quiet %s" (Filename.quote c_path) in
  let exit_code = Sys.command cmd in

  (* Try to read the .v file if it exists *)
  let clight_v =
    if exit_code = 0 && Sys.file_exists v_path then
      Some (slurp_file v_path)
    else
      None
  in

  (* Clean up the temporary .c file.
     Keep the .v file on disk if you want; or remove it if not needed. *)
  (try Sys.remove c_path with _ -> ());

  { ok = exit_code = 0; clight_v; v_path = (if Sys.file_exists v_path then Some v_path else None); cmd }

(* Backwards-compatible boolean API *)
let verify (src : string) : bool =
  let r = clight_of_source ~is_full:false src in
  r.ok
