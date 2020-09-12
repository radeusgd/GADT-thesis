# Differences from the source calculus

The following document describes the differences between the original $\lambda_{2G\mu}$ calculus that is defined on paper and its formalization that I'm developing.
I'm trying to keep the formalization as similar as possible to the original calculus. Most of the simplifications should not affect its expressivity.

> This document is a work in progress.

## Implemented differences

### Pattern Matching

The pattern matching mechanism of the source calculus is pretty sophisticated which complicates not only its formalization but also the translation to pDOT. Many of these complications can be simplified without any loss of expressivity or with only small loss.

#### Nested Patterns

This is mostly a syntactic simplification:
We do not allow constructs similar to
```scala
x match {
  case A(B(x), C(y)) => x + y
  case A(_, _) => 0
}
```

instead such pattern has to be un-nested into

```scala
x match {
  case A(a) =>
    (fst a) match {
      case B(x) =>
        (snd a) match {
          case C(y) => x + y
          case _ => 0
        }
      case _ => 0
    }
}
```

which deconstructs each ADT separately.

Such notation makes the program larger but it does not affect its semantics.

> TODO describe a possible translation and argue why it does not lessen expressivity.
> A source of information on the topic may be compiler optimization papers which sometimes translate nested pattern matching into decision trees which may be equivalent to non-nested exhaustive pattern matches. [Luc Maranget, Compiling Pattern Matching to Good Decision Trees](http://moscova.inria.fr/~maranget/papers/ml05e-maranget.pdf) may be worth looking into may be worth looking into.

#### Determinism

The source calculus actually has a very unusual feature - the pattern matches are defined to execute non-deterministically (see section 2.4, definition 2.2) and can also be stuck.

A match is stuck if no pattern matches the value. But it is also possible that multiple branches may match the value and they are chosen in a non-deterministic manner.

This is actually a very interesting feature, that could be used to implement backtracking algorithms and other interesting applications. However it is hardly related to the topic of GADTs and makes reasoning about the language (and the pDOT translation) **much more complex**. So we decided to remove this determinism, as described in the next section.

I conjecture (_although I won't do that fully formally, I think I will consider writing at least a good paper proof for that if time allows_) that this does not affect the language's expressivity and the non-deterministic variant of the calculus can be simulated by the determinized variant.
A quick proof sketch is to mark the values with a 'present' mark and execute each branch serially: if the first one returns a valid result, it's returned, if the result is not valid (so its evaluation was stuck), the second one is tried and so on. Essentially the backtracking can be simulated manually. This does not handle one other thing - looping, but the source language does not define formally what is the behaviour if one of the alternative branches loops while another would return normally, so given this undefined behaviour we may choose to loop (and only having the non-determinism on stuck branches). Looping can also potentially be handled by implementing executing all branches concurrently, but simulating that is much much harder.

The first approximation of determinization is handled by defining match reduction so that always the first matching clause is chosen. The next section will propose our actual solution.

#### Pattern Exhaustivity

As described above, we want to get rid of non-determinism and also we want to make the patterns as simple as possible.

So we define that the pattern match must handle each available case **exactly once**, that is it not only has to be exhaustive but also it cannot contain duplicate patterns.
This way evaluation never gets stuck (it can still loop), so we can prove the progress lemma.

This does not affect expressivity, since if an original pattern match was not exhaustive, we can add missing branches that include an endless loop (thus simulating 'stuckness').
If there are multiple equivalent patterns, we defined above that the deterministic variant just chooses the first one, so we can discard the missing ones.

Thus the following match:

```scala
enum T {
  case A(a: Int)
  case B(b: String)
  case C(c: Unit)
  case D(d: Unit)
}

(t: T) match {
  case A(a) => (a + 2).toString
  case B(b) => b + "!"
  case B(b) => b + "?"
  case _ => 
}
```

would become

```scala
def loop[A](x: Unit): A = loop[A] ()

(t: T) match {
  case A(a) => (a + 2).toString
  case B(b) => b + "!"
  case C(c) => loop[String] ()
  case D(d) => loop[String] ()
}
```


#### Matching Tuples and Unit

Matching the unit type or tuples was useful when we had nested patterns, as an ADT storing a tuple could have been deconstructed in one go.

Without nested patterns they are useless, since they can be replaced with a simple let statement (and tuples can be deconstructed using the `fst` and `snd` operators).

### Unifying fix-variables with lam-variables

> TODO this one **is** currently implemented but its implications have not been deeply analysed yet.

The source calculus differentiates lam-variables introduced by lambdas and fix-variables introduced by fixpoints.
The distinction is that the lam-variables are treated as values, but fix-variables are not.

At first it may seem strange, since when evaluating a well-typed expression, at the top-level it will never produce a raw variable (a variable in a well-typed expression will be wrapped by some `let` or other constructs that define it). The distrinction is however important, because some terms are well-typed only when their sub-terms are values.
That is the case for example for the `fix` operator and for the $\Lambda$. I have not yet analysed this very deeply, I think it may be a similar concept to pDOT only allowing stable paths in some places.

The formalization currently only has one class of variables which are conservatively treated as not-values (so that the `fix` can be safely used).
I argue that this does not reduce language's expressivity. It does disallow some expressions, for example: $\lambda x: T. \Lambda A. x$ (which has type $T \to \forall_A. T$) is invalid now. But it can easily be fixed by for example introducing abstractions over unit, like: $\lambda x: T. \Lambda A. \lambda u: 1. x$, typing to $T \to \forall_A 1 \to T$, which is a different type, but functionally they are mostly equivalent. They only slightly differ in how they are evaluated, but given the call-by-value semantics of lambdas, this example shouldn't even be affected by this (but others may).

> TODO this argument should be more carefully written and analysed, because of its importance on the rest of the work

## Considered differences

These are differences that are (or were) considered but a decision hasn't been made yet if they should be implemented.

### Single Type-Argument GADTs

The source language does a peculiar design choice - the GADT is parametrized with a list of type arguments, and so is the constructor, but the constructor only takes a single value argument.

This is completely valid, as that single value argument can be a tuple containing any necessary values we may wish to store (or a Unit if we do not wish to store anything) and it helps a lot in the formalization, as handling lists is always more problematic than having just a single value there.

#### GADT type-parameters

Theoretically, one can reduce the amount of GADT type parameters to just one and simply store tuple-types there.
For example, let's look at equality:
```
// original version
enum Eq[A, B] {
  case Refl[C] extends Eq[C, C]
}

val ev: Eq[T, U] // evidence that T =:= U
ev match {
  case Refl[C] => // here we can use the fact that T =:= C =:= U
}

// version with just one type parameter
enum Eq[A] {
  case Refl[C] extends Eq[C * C]
}

val ev: Eq[T * U]
ev match {
  case Refl[C] => // here we know that C * C =:= T * U but that should entail T =:= C =:= U
}
```

> **Important Objection**: It seems like the source language does not define type equality in such a way that equality of two tuple-types can automatically entail equality of their respective elements (see Figure 7 in the paper), but I may understand something wrongly here. I definitely need to revise this aspect of the paper as it will soon be very important when defining the type-equality entailment relation. TODO


#### Constructors

I conjecture that constructors must allow for multiple type arguments to not reduce the expressivity greatly.

We could also use type-tuples in the constructors, but we cannot since we do not have subtyping or type-classes in the source language, we cannot restrict the type arguments in any way.

For example:
```
enum Foo[A] {
  case Bar[C] extends Foo[C * C]
}


something match {
  case Case[T] =>  // hmmm [that example is a work in progress]
}
```

> hmm TODO maybe it is not a problem? but I'm pretty sure intuitively that this limits our possibilities. Counterexamples should be explored.
