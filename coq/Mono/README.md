# Monomorphic Type-Inference

This is a simply-typed lambda-caluclus extended with numeric & boolean arithmetic.
The syntax is given in ***Curry-style***, i.e. w/o type-annotations given in term-abstractions.

Here are formal definitions of constraint generation and unification as described in
[Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/),
as well as corresponding computable functions.

The constraint generation rules are defined in
reference to a declarative typing semantics, and should be "equivalent".

## Proven Results

- Soundness of constraint generation with respect to declarative typing (`Mono.v`).
- Soundness of computable constraint generation
with respect to the ***`Inductive`*** definition (`MonoComputable.v`).

## In Progress

Completeness results have proved much more elusive than their soundness counterparts.
- Completeness of constraint generation with respect to declarative typing (`MonoCompleteness.v`).
- Completeness of computable constraint generation
with respect to the ***`Inductive`*** definition (`MonoComputable.v`).
- Adding `let` expressions to the language, albeit w/o ***`let`-polymorphism***.