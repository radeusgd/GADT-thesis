# GADT-thesis

[![Compile the Proofs](https://github.com/radeusgd/GADT-thesis/actions/workflows/main.yml/badge.svg)](https://github.com/radeusgd/GADT-thesis/actions/workflows/main.yml)

This is the repository containing Coq proofs attached to my master's thesis.

- [lambda 2Gmu](./lambda2Gmu/) - my formalization of the source calculus
  - [Definitions](./lambda2Gmu/Definitions.v) define the calculus syntax, typing and semantics and states the desired safety properties
  - [Prelude](./lambda2Gmu/Prelude.v) gathers some basic useful lemmas
  - [Infrastructure](./lambda2Gmu/Infrastructure.v) proves syntactic properties of binder handling
  - [Regularity](./lambda2Gmu/Regularity.v) proves basic properties of the type system, with the most important result - a well typed term has other properties we defined (its type is well formed, it is closed etc.)
  - [CanonicalForms](./lambda2Gmu/CanonicalForms.v) has proofs that allow to deconstruct a value of a given type to its canonical form
  - [Progress](./lambda2Gmu/Progress.v) proves the progress theorem
  - [Preservation](./lambda2Gmu/Preservation.v) proves the preservation theorem
- [annotated lambda 2Gmu](./lambda2Gmu_annotated/) - formalization of the annotated variant of the calculus (as described in Section 5.3). The soundness proof is a copy of the standard version with minor adaptations in a few lemmas to accommodate for the added annotations.
- [pDOT translation](./translation_pdot/) - proofs associated with the translation attempts. Includes lemmas characterizing pDOT's subtyping.
  - [RuleTests][./translation_pdot/RuleTests.v] - contains lemmas showing how some too general rules would break soundness.
  - [TestEqualityEnv](./translation_pdot/TestEqualityEnv.v) - manually translated environment for the Eq GADT
  - [TestEquality](./translation_pdot/TestEquality.v) - typing proofs for `coerce` and `transitivity` terms using the Eq GADT
- [extended pDOT translation](./translation_extended/) - proofs associated with the translation attempts using the extended pDOT calculus
  - [TestEquality](./translation_extended/TestEquality.v) - typing proofs for `coerce` and `transitivity` terms using the Eq GADT
  - [TestEquality2](./translation_extended/TestEquality2.v) - typing proof for the `destruct` term which was not typeable in original pDOT, as described in Chapter 6

## Building the proofs

The proofs require Coq 8.13.0 and the TLC library. The easiest way to obtain them is to use OPAM:

```
opam repo add coq-released http://coq.inria.fr/opam/released
opam pin add coq 8.13.0
opam install -j4 coq-tlc
```

The next step is to prepare the dependencies - the standard and extended formalizations of pDOT. This can be done by running the script `refresh_dependencies.sh`.

Each subproject can be compiled by running `make` in its corresponding subdirectory.
However, the sub-projects depend on each other, so `lambda2Gmu` should be compiled before `lambda2Gmu_annotated` and both of these subprojects should be compiled before `translation_pdot` or `translation_extended`.

## Useful links

- [Public repo](https://github.com/radeusgd/pDOT-GADT) - the repo where I put finished documents and other deliverables that I want to share
- [pDOT repo](https://github.com/amaurremi/dot-calculus/tree/master/src/extensions/paths) - formalization of the target calculus, pDOT that I will want to base on
- [Localy Nameless library](https://www.chargueraud.org/softs/ln/) - used for handling binders in calculus proofs, a hybrid approach connecting DeBruijn indices for closed terms and named variables for free terms; using cofinite quantification
- [TLC library](https://www.chargueraud.org/softs/tlc/) - a non-constructive library for Coq, used in pDOT proofs (Locally Nameless is a part of it)
- [Extended pDOT repo](https://github.com/Linyxus/extended-pdot-calculus) - the repository containing the extended variant of pDOT, as described in Section 6.2.2 of the thesis.

## Papers
- [A Path to DOT](https://arxiv.org/abs/1904.07298) - the paper describing pDOT
- [Guarded Recursive Datatype Constructors paper](http://cs-www.bu.edu/fac/hwxi/academic/papers/popl03.pdf) by Xi et al., defining my source calculus
