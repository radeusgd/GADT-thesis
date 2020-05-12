# GADT-thesis

This is my private repo where I put Work In Progress works on my master's thesis.

[experiments/](experiments/) currently contains my attempt at formalizing the λ2Gμ calculus

## Useful links

- [Public repo](https://github.com/radeusgd/pDOT-GADT) - the repo where I put finished documents and other deliverables that I want to share
- [pDOT repo](https://github.com/amaurremi/dot-calculus/tree/master/src/extensions/paths) - formalization of the target calculus, pDOT that I will want to base on
- [Localy Nameless library](https://www.chargueraud.org/softs/ln/) - used for handling binders in calculus proofs, a hybrid approach connecting DeBruijn indices for closed terms and named variables for free terms; using cofinite quantification
- [TLC library](https://www.chargueraud.org/softs/tlc/) - a non-constructive library for Coq, used in pDOT proofs (Locally Nameless is a part of it)

## Papers
- [A Path to DOT](https://arxiv.org/abs/1904.07298) - the paper describing pDOT
- [Guarded Recursive Datatype Constructors paper](http://cs-www.bu.edu/fac/hwxi/academic/papers/popl03.pdf) by Xi et al., defining my source calculus

## Useful reference materials
- [Nested Inductive types](http://adam.chlipala.net/cpdt/html/InductiveTypes.html#lab32) - how to define recursion/induction schemes for more complex inductive types
- [Quoted Pattern Matching proof](https://github.com/radeusgd/QuotedPatternMatchingProof) - my proof of the Quoted Pattern Matching calculus safety, for reference
