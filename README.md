Coq 8.19.2
coq-compcert 3.15
coq-vst 2.15
frama-c.31.0

# Idea:
1. Take query, get response C code from LLM.
2. Use compcert to get coq representation of C code (Clight)
3. Try VST to verify algorithm
4. If that doesn't work ask LLM to generate proof.
5. if this runs, it is valid code and we return it to user
6. If it fails we retry proofs / generating code w/ max timeout. If it times out we tell the user we could not verify the code (we could still return it though).

# Requirements:
Ocaml:
-dream
-yojson

# Get into Environment
1. opam switch list
2. opam switch double-check

# Comp-Cert Setup
opam install coq-compcert.3.15
opam install coq-vst.2.15
clightgen -normalize -o vst_test1.v test.c

# Frama Setup
opam install frama-c alt-ergo
frama-c -wp -wp-status-all -wp-rte -wp-prover alt-ergo frama_test_max_array.c