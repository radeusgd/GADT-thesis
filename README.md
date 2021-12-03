# GADT-thesis

[![Compile the Proofs](https://github.com/radeusgd/GADT-thesis/actions/workflows/main.yml/badge.svg)](https://github.com/radeusgd/GADT-thesis/actions/workflows/main.yml)

This is the repository containing Coq proofs attached to my master's thesis.

## Structure of the repository

- [lambda2Gmu](https://radeusgd.github.io/GADT-thesis/latest/lambda2Gmu/toc.html) - my formalization of the source calculus λ2Gμ
  - [Definitions.v](https://radeusgd.github.io/GADT-thesis/latest/lambda2Gmu/GMu.Definitions.html) define the calculus syntax, typing and semantics and states the desired safety properties
  - [Infrastructure.v](https://radeusgd.github.io/GADT-thesis/latest/lambda2Gmu/GMu.Infrastructure.html) proves syntactic properties of binder handling
  - [Regularity.v](https://radeusgd.github.io/GADT-thesis/latest/lambda2Gmu/GMu.Regularity.html) proves basic properties of the type system, with the most important result - a well typed term has other properties we defined (its type is well formed, it is closed etc.)
  - [CanonicalForms.v](https://radeusgd.github.io/GADT-thesis/latest/lambda2Gmu/GMu.CanonicalForms.html) has proofs that allow to deconstruct a value of a given type to its canonical form
  - [Progress.v](https://radeusgd.github.io/GADT-thesis/latest/lambda2Gmu/GMu.Progress.html) proves the progress theorem
  - [Preservation.v](https://radeusgd.github.io/GADT-thesis/latest/lambda2Gmu/GMu.Preservation.html) proves the preservation theorem
- [lambda2Gmu_annotated](https://radeusgd.github.io/GADT-thesis/latest/lambda2Gmu_annotated/toc.html) - formalization of the annotated variant of the calculus (as described in Section 5.3). The soundness proof is a copy of the standard version with minor adaptations in a few lemmas to accommodate for the added annotations.
- [translation_pdot](https://radeusgd.github.io/GADT-thesis/latest/translation_pdot/toc.html) - proofs associated with the translation attempts. Includes lemmas characterizing pDOT's subtyping.
  - [RuleTests.v](https://radeusgd.github.io/GADT-thesis/latest/translation_pdot/Top.RuleTests.html) - contains lemmas showing how some too general rules would break soundness.
  - [TestEqualityEnv.v](https://radeusgd.github.io/GADT-thesis/latest/translation_pdot/Top.TestEqualityEnv.html) - manually translated environment for the Eq GADT
  - [TestEquality.v](https://radeusgd.github.io/GADT-thesis/latest/translation_pdot/Top.TestEquality.html) - typing proofs for `coerce` and `transitivity` terms using the Eq GADT
- [translation_extended](https://radeusgd.github.io/GADT-thesis/latest/translation_extended/toc.html) - proofs associated with the translation attempts using the extended pDOT calculus
  - [TestEquality.v](https://radeusgd.github.io/GADT-thesis/latest/translation_extended/Top.TestEquality.html) - typing proofs for `coerce` and `transitivity` terms using the Eq GADT
  - [TestEquality2.v](https://radeusgd.github.io/GADT-thesis/latest/translation_extended/Top.TestEquality2.html) - typing proof for the `destruct` term which was not typeable in original pDOT, as described in Chapter 6
- [tools](./tools/) contains tools helping with working with the Lambda2Gmu formalization, written in Scala.
  It features a parser for Lambda2Gmu pseudocode in a human-readable syntax (close to the syntax defined on paper),
  a transpiler which converts name-based binders to De Bruijn indices and allows to convert the human-readable syntax
  to Coq terms compatible with the formalization.

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
