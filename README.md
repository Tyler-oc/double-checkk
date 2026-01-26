# What is double checkk?

Double checkk is a VS code extension designed to ensure your C code works perfectly using Frama-C. To do this, double-checkk takes your code, and uses whatever LLM you choose to annotate your code in Frama-C. If it doesn't compile, then you can see exactly where it went wrong and rewrite your code if you so choose. If it compiles, then you can gaurantee your code is up to the specs that you desire.

# requirement
frama-c.31.0

# Frama Setup

opam install frama-c alt-ergo
little problems: frama-c -wp -wp-status-all -wp-rte -wp-prover z3 frama_test_max_array.c
big boy problems: frama-c -wp -wp-rte -wp-prover z3,alt-ergo,cvc5 -wp-par 4 -wp-timeout 15 frama_test3_fac2.c
(Currently testing this benchmark: https://github.com/cverified/cbench)

# BE IN FRONTEND FOLDER
npm ci;

npm run watch;

In src/extension.ts
f5





