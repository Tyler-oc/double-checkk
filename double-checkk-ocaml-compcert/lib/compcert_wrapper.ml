(* my_compcert_wrapper.ml *)

open Clightgen
open Clight

let verify (src : string) : bool =
  (* Write the code to a temporary file, since Clightgen works on files *)
  let tmp_file = Filename.temp_file "doublecheckk" ".c" in
  let oc = open_out tmp_file in
  output_string oc src;
  close_out oc;

  (* Call Clightgen to parse and translate *)
  match Clightgen.parse tmp_file with
  | Ok (program, _) ->
      (* If we reach here, parsing/translation succeeded. *)
      (* [program] is a Clight AST. You could do more checks. *)
      true
  | Error msg ->
      (* Parsing or translation failed *)
      prerr_endline ("CompCert error: " ^ msg);
      false
