(* Frama_c_wrapper: verify C code with Frama-C via an LLM-generated ACSL step.
   The public API returns only a boolean: true if Frama-C accepts it (parses/typechecks),
   false otherwise. The ACSL text is never exposed outside this module. *)

(* ---- Prompt building ---- *)

let build_prompt ~(source:string) ~(specs:string) : string =
  Printf.sprintf
{|

Example 1: """ /*@ requires length > 0; requires \valid_read(arr + (0..length-1)); assigns \nothing; ensures \exists integer k; 0 <= k < length && \result == arr[k]; ensures \forall integer i; 0 <= i < length ==> \result >= arr[i]; */ int find_max(int arr[], int length) { int max = arr[0]; /*@ loop invariant 0 <= i <= length; loop invariant \forall integer j; 0 <= j < i ==> max >= arr[j]; loop invariant \exists integer k; 0 <= k < length && max == arr[k]; loop assigns i, max; loop variant length - i; */ for(int i = 1; i < length; i++) { if (arr[i] > max) { max = arr[i]; } } return max; } /*@ assigns \nothing; */ int main() { int arr[] = {1, 2, 4, 2, 8, 3}; int length = 6; int result = find_max(arr, length); return 0; }""" 
  
Example 2: """ /*@ logic integer factorial(integer n) = (n <= 0) ? 1 : n * factorial(n - 1); */ /*@ requires n >= 0; requires n <= 12; assigns \nothing; ensures \result == factorial(n); */ int compute_factorial(int n) { int i, f; f = 1; /*@ loop invariant 1 <= i <= n + 1; loop invariant f == factorial(i - 1); loop invariant f >= 1; loop invariant 1 <= i <= 13; loop invariant i == 1 ==> f == 1; loop invariant i == 2 ==> f == 1; loop invariant i == 3 ==> f == 2; loop invariant i == 4 ==> f == 6; loop invariant i == 5 ==> f == 24; loop invariant i == 6 ==> f == 120; loop invariant i == 7 ==> f == 720; loop invariant i == 8 ==> f == 5040; loop invariant i == 9 ==> f == 40320; loop invariant i == 10 ==> f == 362880; loop invariant i == 11 ==> f == 3628800; loop invariant i == 12 ==> f == 39916800; loop invariant i == 13 ==> f == 479001600; loop assigns i, f; loop variant n - i + 1; */ for (i = 1; i <= n; i++) f = f * i; return f; } /*@ assigns \nothing; */ int main() { int n = 5, i, f; f = 1; /*@ loop invariant 1 <= i <= n + 1; loop invariant f == factorial(i - 1); loop invariant f >= 1; loop invariant i == 1 ==> f == 1; loop invariant i == 2 ==> f == 1; loop invariant i == 3 ==> f == 2; loop invariant i == 4 ==> f == 6; loop invariant i == 5 ==> f == 24; loop invariant i == 6 ==> f == 120; loop assigns i, f; loop variant n - i + 1; */ for (i = 1; i <= n; i++) f = f * i; return f; }""" 

Example 3: """ /*@ logic integer factorial(integer n) = (n <= 0) ? 1 : n * factorial(n - 1); */ /*@ assigns \nothing; ensures \result == factorial(5); */ int main() { int s, r, n = 5, u, v; /* keep an explicit runtime/verification check for n bounds */ /*@ assert 0 <= n <= 12; */ /* Outer loop: - r runs from 1 up to n-1, - u == factorial(r) at loop head */ /*@ loop invariant 1 <= r <= n; loop invariant u == factorial(r); loop assigns r, s, u, v; loop variant n - r; */ for (u = r = 1; r < n; r++) { v = u; /* Inner loop rewritten as a simple counting loop: u += v executed r times */ /*@ loop invariant 0 <= s <= r; loop invariant u == v * (s + 1); loop assigns s, u; loop variant r - s; */ for (s = 0; s < r; ++s) { u += v; } /* now u == v * (r + 1) == factorial(r+1) */ /*@ assert u == factorial(r + 1); */ } return u; }""" 

You are an expert in Frama-C/ACSL. Please verify this code using Frama-C/ACSL """void spawn_food(Food *f, Snake *s) { int valid; do { valid = 1; f->pos.x = rand() % (WIDTH - 2) + 1; f->pos.y = rand() % (HEIGHT - 2) + 1; for (int i = 0; i < s->length; i++) { if (f->pos.x == s->body[i].x && f->pos.y == s->body[i].y) { valid = 0; break; } } } while (!valid); }
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
