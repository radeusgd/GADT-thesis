# GADT-thesis

This is the repository containing Coq proofs attached to my master's thesis.

- [lambda 2Gmu](./lambda2Gmu/) - my formalization of the source calculus
  - [Definitions](./lambda2Gmu/Definitions.v) define the calculus syntax, typing and semantics and states the desired safety properties
  - [Prelude](./lambda2Gmu/Prelude.v) gathers some basic useful lemmas
  - [Infrastructure](./lambda2Gmu/Infrastructure.v) proves syntactic properties of binder handling
  - [Regularity](./lambda2Gmu/Regularity.v) proves basic properties of the type system, with the most important result - a well typed term has other properties we defined (its type is well formed, it is closed etc.)
  - [CanonicalForms](./lambda2Gmu/CanonicalForms.v) has proofs that allow to deconstruct a value of a given type to its canonical form
  - [Progress](./lambda2Gmu/Progress.v) proves the progress theorem
  - [Preservation](./lambda2Gmu/Preservation.v) proves the preservation theorem

## Useful links

- [Public repo](https://github.com/radeusgd/pDOT-GADT) - the repo where I put finished documents and other deliverables that I want to share
- [pDOT repo](https://github.com/amaurremi/dot-calculus/tree/master/src/extensions/paths) - formalization of the target calculus, pDOT that I will want to base on
- [Localy Nameless library](https://www.chargueraud.org/softs/ln/) - used for handling binders in calculus proofs, a hybrid approach connecting DeBruijn indices for closed terms and named variables for free terms; using cofinite quantification
- [TLC library](https://www.chargueraud.org/softs/tlc/) - a non-constructive library for Coq, used in pDOT proofs (Locally Nameless is a part of it)
- [Extended pDOT repo](https://github.com/Linyxus/extended-pdot-calculus) - the repository containing the extended variant of pDOT, as described in Section 6.2.2 of the thesis.

## Papers
- [A Path to DOT](https://arxiv.org/abs/1904.07298) - the paper describing pDOT
- [Guarded Recursive Datatype Constructors paper](http://cs-www.bu.edu/fac/hwxi/academic/papers/popl03.pdf) by Xi et al., defining my source calculus
