# Future ideas

This is a wish-list of ideas/results that we want to formalize.

## Completeness of the DLO theory

This is a **hard** problem.

Completeness says that everything that is true in ℚ can be proved from
`DLO_axioms`. Said differently, if something is true for ℚ then it is true
for every model for `DLO_axioms` (because they all have the same theory).


### Progress so far
- we have a definition of `DLO_axioms`, but not of `DLO_theory` in `examples.lean`.
- we have a definition of completeness.
- we need to state the completeness of DLO theory as a theorem.

🚀 *Next TODO:* Define `DLO_theory` in `examples.lean`.


## Vaught's theorem
We are close to finishing the proof (assuming Lownheim-Skolem as an axiom).

🚀 *Next TODO:* Finish the proof of Vaught's theorem.


## Godel encoding (Abandoned)
This is a map from ℕ to the long strings encoding prime factorization.
This was becoming too hard so we abandoned it. All the partial definitions
we made are currently in `godel_encoding.lean`.

## Quantifier elimination in DLO theory
There is currently an open issue regarding this here:
[issues/41](https://github.com/vaibhavkarve/igl2020/issues/41)

🚀 *Next TODO*: Close issue #41.


## Definability and o-minimality

Examples/notes/thoughts:
- x<2 in ℝ defines (-∞, 2)
- x=y in ℝ defines a line at 45 degrees.
- Non-definable: (ℤ, +). ∃x, x+x=x defines {0}. Cannot define {1}.
- Is ℤ definable?
- Are even numbers (ℤ, +) ∃ y, x=y+y → (ℤ, +) is not o-minimal.

🚀 *Next TODO*: Not sure. Need to figure out what the Next TODO is.


## Los' theorem
This uses something called [ultraproducts](https://en.wikipedia.org/wiki/Ultraproduct)

Los' theorem implies compactness and Loewenheim-Skolem.

🚀 *Next TODO*: Define ultraproducts.
