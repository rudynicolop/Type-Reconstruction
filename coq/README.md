# Verified Type-Reconstruction/Inference

This directory is intended as a formal-basis for the implementations in the rest of the repository.
While it is unlikely I will feel compelled to extract the computable functions to **`OCaml`** or **`Haskell`**,
the implementations here will at least provide some (informal) assurances of the correctness of
my other implementations, which will be (mostly) identical to the code found here.

## Monomorphic Type-Inference

This is a simply-typed lambda-caluclus extended with numeric & boolean arithmetic.
The syntax is given in ***Curry-style***, i.e. w/o type-annotations given in term-abstractions.

Here are formal definitions of constraint generation and unification as described in
[Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/),
as well as corresponding computable functions.

The constraint generation rules are defined in
reference to a declarative typing semantics, and should be "equivalent".

### Proven Results

- Soundness of constraint generation with respect to declarative typing (`Mono.v`).
- Soundness of computable constraint generation
with respect to the ***`Inductive`*** definition (`MonoComputable.v`).

### In Progress

Completeness results have proved much more elusive than their soundness counterparts.
- Completeness of constraint generation with respect to declarative typing (`MonoCompleteness.v`).
- Completeness of computable constraint generation
with respect to the ***`Inductive`*** definition (`MonoComputable.v`).
- Termitation of the unification algorithm (`Unify.v`).
- Adding `let` expressions to the language, albeit with/o ***`let`-polymorphism***.
