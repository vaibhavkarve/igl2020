import tactic
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
(M : Type)                                -- universe/domain
(F (f : L.F) : vector M (L.n_f f) → M)   -- interpretation of each function
(R (r : L.R) : set (vector M (L.n_r r)))  -- interpretation of each relation
(C : L.C → M)                            -- interpretation of each constant
