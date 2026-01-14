frama-c.31.0

# Idea:

1. Take query, get response C code from LLM.
2. Use compcert to get coq representation of C code (Clight)
3. Try VST to verify algorithm
4. If that doesn't work ask LLM to generate proof.
5. if this runs, it is valid code and we return it to user
6. If it fails we retry proofs / generating code w/ max timeout. If it times out we tell the user we could not verify the code (we could still return it though).

# Frama Setup

opam install frama-c alt-ergo
little problems: frama-c -wp -wp-status-all -wp-rte -wp-prover z3 frama_test_max_array.c
big boy problems: frama-c -wp -wp-rte -wp-prover z3,alt-ergo,cvc5 -wp-par 4 -wp-timeout 15 frama_test3_fac2.c
(Currently testing this benchmark: https://github.com/cverified/cbench)

BE IN FRONTEND FOLDER
npm ci
npm run watch

In extension.ts
f5

