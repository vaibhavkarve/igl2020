import tactic
import data.real.basic
import set_theory.cardinal
/- This is an attempt to define Languages and Structures on these
   Languages.-/


/-A language is given by specifying functions, relations and constants
along with the arity of each function and each relation.-/
structure lang :=
(F : Type)      -- functions
(n_f : F → ℕ)  -- arity of each function
(R : Type)      -- relations
(n_r : R → ℕ)  -- arity of each relation
(C : Type)      -- constants

/-We now define some example languages. We start with the simplest
possible language, the language of pure sets. This language has no
functions, relations or constants.-/
def set_lang : lang :=
begin
  fconstructor, -- we will construct the lang by specifying its fields.
  use empty,    -- empty is the name of the empty type (0 elements)
  use (λ_, 0),  -- doesn't matter. Vacuous definition.
  use empty,    -- empty type because no relations.
  use (λ _, 0), -- doesn't matter. Vacuous definition.
  use empty,    -- empty type because no constants.
end

/-A magma is a {×}-structure. So this has 1 function, 0 relations and
0 constants.-/
def magma_lang : lang :=
begin
  fconstructor,
  use unit,     -- unit is the name of the type with only 1 member.
  use (λ _, 2), -- this member is a binary operation
  use empty,    -- no relations.
  use (λ _, 0), -- vacuous definition.
  use empty     -- no constants
end

/-A semigroup is a {×}-structure which satisfies the identity
  u × (v × w) = (u × v) × w-/
def semigroup_lang : lang :=
begin
  fconstructor,
  use unit,     -- one function, therefore we use unit
  use (λ _, 2), -- the function is a binary operation 
  use unit,     -- one relation, therefore we use unit
  use (λ _, 3), -- the relation is ternary (uses u, v, w)
  use empty,    -- no constants.
end

/- A monoid is a {×, 1}-structure which satisfies the identities
   1. u × (v × w) = (u × v) × w
   2. u × 1 = u
   3. 1 × u = u. -/
def monoid_lang : lang := sorry

/- A group is a {×, ⁻¹, 1}-structure which satisfies the identities
 1. u × (v × w) = (u × v) × w
 2. u × 1 = u
 3. 1 × u = u
 4. u × u−1 = 1
 5. u−1 × u = 1 -/
def group_lang : lang := sorry

/- A semiring is a {×, +, 0, 1}-structure which satisfies the identities
  1. u + (v + w) = (u + v) + w
  2. u + v = v + u
  3. u + 0 = u
  5. u × (v × w) = (u × v) × w
  6. u × 1 = u, 1 × u = u
  7. u × (v + w) = (u × v) + (u × w)
  8. (v + w) × u = (v × u) + (w × u)-/
def semiring_lang : lang := sorry

/- A ring is a {×,+,−,0,1}-structure which satisfies the identities
   1. u + (v + w) = (u + v) + w
   2. u + v = v + u
   3. u + 0 = u
   4. u + (−u) = 0
   5. u × (v × w) = (u × v) × w
   6. u × 1 = u, 1 × u = u
   7. u × (v + w) = (u × v) + (u × w)
   8. (v + w) × u = (v × u) + (w × u)-/
def ring_lang : lang := sorry


/- We now define an L-structure to be interpretations of functions,
 relations and constants. -/
structure struc (L : lang) :=
(univ : Type)                                  -- universe/domain
(F (f : L.F) : vector univ (L.n_f f) → univ)  -- interpretation of each function
(R (r : L.R) : set (vector univ (L.n_r r)))    -- interpretation of each relation
(C : L.C → univ)                              -- interpretation of each constant



/-An L-embedding is a map between two L-structures that is injective
  on the domain and preserves the interpretation of all the symbols of
  L.-/
structure embedding {L : lang} (M N : struc L) : Type :=
(η : M.univ → N.univ)                           -- map of underlying domains
(η_inj : function.injective η)                   -- should be one-to-one
(η_F : ∀ f v,                                    -- preserves action of each function
     η (M.F f v) = N.F f (vector.map η v))
(η_R : ∀ r v,                                    -- preserves each relation
     v ∈ (M.R r) ↔ (vector.map η v) ∈ (N.R r))
(η_C : ∀ c,                                      -- preserves each constant
     η (M.C c) = N.C c)




/-A bijective L-embedding is called an L-isomorphism.-/
structure isomorphism {L: lang} (M N : struc L) extends (embedding M N) : Type :=
(η_bij : function.bijective η)


/-The cardinality of a struc is the cardinality of its domain.-/
def card {L : lang} (M : struc L) : cardinal := cardinal.mk M.univ

/-If η: M → N is an embedding, then the cardinality of N is at least
  the cardinality of M.-/
lemma le_card_of_embedding {L : lang} (M N : struc L) (η : embedding M N) :
  card M ≤ card N :=
begin
  sorry  -- Look for a theorem in mathlib that guarantees the result
         -- using injectivity of η.
end
