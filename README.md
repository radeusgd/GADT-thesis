# GADT-thesis

This is my private repo where I put Work In Progress works on my master's thesis.

- [lambda 2Gmu](./lambda2Gmu/) - my formalization of the source calculus
- [Source calculus differences](notes/source-calculus-differences.md) explains differences between the paper version of the calculus and the formalization.

> It is a good idea to install an extension rendering TeX markers ([for example](https://chrome.google.com/webstore/detail/tex-all-the-things/cbimabofgmfdkicghcadidpemeenbffn?hl=en)) when browsing Markdown documents on GitHub in this repository.

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

## My local links
- [TLC sources](~/.opam/system/lib/coq/user-contrib/TLC/) - quick access to TLC documentation
  + [TLC LibEnv](~/.opam/system/lib/coq/user-contrib/TLC/LibEnv.v)
  + [TLC LibLN](~/.opam/system/lib/coq/user-contrib/TLC/LibLN.v)
  + [Fsub soundness in TLC](../CoqLibs/formalmetacoq/ln/Fsub_Soundness.v)
- [pDOT proof](../dot-calculus/src/extensions/paths/) - quick access to the pDOT proof
  + [pDOT Definitions](../dot-calculus/src/extensions/paths/Definitions.v)
