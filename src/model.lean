import tactic
import data.real.basic
import set_theory.cardinal
/- This is an attempt to define Languages and Structures on these
   Languages.-/



-- -----------------------------------------------------------------
-- 1. Languages and Examples
-- -----------------------------------------------------------------

/-A language is given by specifying functions, relations and constants
along with the arity of each function and each relation.-/
structure lang : Type 1 :=
(F : Type)      -- functions
(n_f : F → ℕ)  -- arity of each function
(R : Type)      -- relations
(n_r : R → ℕ)  -- arity of each relation
(C : Type)      -- constants


/-We now define some example languages. We start with the simplest
possible language, the language of pure sets. This language has no
functions, relations or constants.-/
def set_lang: lang := ⟨empty, (λ_, 1000), empty, (λ_, 0), empty⟩

/-A magma is a {×}-structure. So this has 1 function, 0 relations and
0 constants.-/
def magma_lang : lang := {F := unit,
                          n_f := (λ star, 2), ..set_lang} 



/-A semigroup is a {×}-structure which satisfies the identity
  u × (v × w) = (u × v) × w-/
def semigroup_lang : lang :=
begin
  fconstructor,
  exact unit,                -- one function, therefore we use unit
  exact function.const _ 2,  -- the function is a binary operation 
  exact unit,                -- one relation, therefore we use unit
  exact function.const _ 3,  -- the relation is ternary (uses u, v, w) 
  exact empty,               -- no constants.
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


-- -----------------------------------------------------------------
-- 2. Structures and Examples
-- -----------------------------------------------------------------


/- We now define an L-structure to be interpretations of functions,
 relations and constants. -/
structure struc (L : lang) : Type 1 :=
(univ : Type)                                  -- universe/domain
(F (f : L.F) : vector univ (L.n_f f) → univ)  -- interpretation of each function
(R (r : L.R) : set (vector univ (L.n_r r)))    -- interpretation of each relation
(C : L.C → univ)                              -- interpretation of each constant



/-We can show that Mathlib's group structure is a struc on group_lang.-/

lemma type_is_struc_of_set_lang {A : Type} : struc (set_lang) :=
begin
  fconstructor,
   { exact A},
   { intros f,
     cases f},
   { intros r,
     cases r},
   { intros c,
     cases c},
 end

/-We need to define a magma, because it looks like it is not defined
  in Mathlib.-/
class magma (α : Type) :=
(mul : α → α → α)


lemma free_magma_is_struc_of_magma_lang {A : Type} [magma A] :
  struc (magma_lang) :=
begin
  fconstructor,
    { exact A},
    { intros _ v,
      change magma_lang.n_f f with 2 at v,
      exact magma.mul (v.nth 0) (v.nth 1)},
    { sorry},
    { sorry},
end


lemma semigroup_is_struc_of_semigroup_lang {A : Type} [semigroup A] :
  struc (semigroup_lang) :=
begin
  fconstructor,
    { exact A},
    { intros f v,
      change semigroup_lang.n_f f with 2 at v,
      exact semigroup.mul (v.nth 0) (v.nth 1)},
    { sorry},
    { sorry}
end

lemma monoid_is_struc_of_monoid_lang {A : Type} [monoid A] :
  struc (monoid_lang) := sorry
lemma group_is_struc_of_group_lang {A : Type} [group A] :
  struc (group_lang) := sorry
lemma semiring_is_struc_of_semiring_lang {A : Type} [semiring A] :
  struc (semiring_lang) := sorry
lemma ring_is_struc_of_ring_lang {A : Type} [ring A] :
  struc (ring_lang) := sorry



-- -----------------------------------------------------------------
-- 3. Embeddings between Structures
-- -----------------------------------------------------------------


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


-- -----------------------------------------------------------------
-- 4. Terms
-- -----------------------------------------------------------------

/-We need a type to represent variables.-/
constant var : Type

/- We define terms in a language to be constants, variables or
   functions acting on terms.-/
inductive term (L : lang) : Type
| const : L.C → term
| var : var → term
| func (f : L.F) : list term → term


variables (A : Type) (B : Type)