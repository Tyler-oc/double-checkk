(* Frama_c_wrapper: verify C code with Frama-C via an LLM-generated ACSL step.
   The public API returns only a boolean: true if Frama-C accepts it (parses/typechecks),
   false otherwise. The ACSL text is never exposed outside this module. *)

(* ---- Prompt building ---- *)

let build_prompt ~(source:string) ~(specs:string) : string =
  Printf.sprintf
    {|You are an expert in Frama-C/ACSL.

Given this C code:
---
%s
---

Given these verification specs:
---
%s
---

Task:
1) Produce ACSL annotations/contracts for the code to satisfy the specs.
2) Integrate the ACSL at the correct locations (as function contracts or global annotations)
   so that Frama-C can parse and type-check the result.
3) Return the FULL C FILE with ACSL inline (not just snippets). Do not include extra text,
   only the compilable C+ACSL source code.
|}
    source specs


let call_llm (_prompt:string) : (string, string) result =
  (* Placeholder: return an error until implemented. *)
  Error "LLM call not implemented"


let write_temp ~(suffix:string) (content:string) : string =
  let path = Filename.temp_file "doublecheckk" suffix in
  let oc = open_out path in
  output_string oc content;
  close_out oc;
  path

let frama_c_cmd () =
  (* If running outside an opam env, use opam exec to locate frama-c. *)
  match Sys.getenv_opt "OPAM_SWITCH_PREFIX" with
  | Some _ -> "frama-c"
  | None -> "opam exec -- frama-c"

let run_frama_c (c_path:string) : int =
  let cmd = Printf.sprintf "%s -quiet %s" (frama_c_cmd ()) (Filename.quote c_path) in
  Sys.command cmd


(* verify: returns true iff Frama-C accepts the combined C+ACSL. *)
let verify (source:string) (specs:string) : bool * string option =
  match call_llm (build_prompt ~source ~specs) with
  | Error _err ->
      (false, None)
  | Ok llm_text ->
      let c_path = write_temp ~suffix:".c" llm_text in
      let exit_code =
        try run_frama_c c_path
        with _ -> 1
      in
      (try Sys.remove c_path with _ -> ());
      (exit_code = 0, Some llm_text)
