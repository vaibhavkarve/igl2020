import tactic
import data.real.basic
import set_theory.cardinal
/-!
1. We define languages and give examples.
2. We define structures and give examples.
3. We define embedding between two structures on the same language.
4. (WIP) We define variables, terms, and formulas.
-/



/-! -----------------------------------------------------------------
-- 1. Languages and Examples
-- ----------------------------------------------------------------/

/-- A language is given by specifying functions, relations and constants
along with the arity of each function and each relation.-/
structure lang : Type 1 :=
(F : ℕ → Type)    -- functions
(R : ℕ → Type)    -- relations
(C : Type)          -- constants


/-- We now define some example languages. We start with the simplest
possible language, the language of pure sets. This language has no
functions, relations or constants.-/
def set_lang: lang := ⟨function.const ℕ empty,
                       function.const ℕ empty,
                       empty⟩

/-- The language of ordered sets is the language or sets with a binary
  ordering relation {<}.-/
def ordered_set_lang: lang := {R := λ n : ℕ, if n=2 then unit else empty,
                               ..set_lang}

/-- A magma is a {×}-structure. So this has 1 function, 0 relations and
0 constants.-/
def magma_lang : lang := {F := λ n : ℕ, if n=2 then unit else empty,
                          ..set_lang}


/-- A semigroup is a {×}-structure which satisfies the identity
  u × (v × w) = (u × v) × w.  Note that identities are note relations!-/
def semigroup_lang : lang := magma_lang

/-- A monoid is a {×, 1}-structure which satisfies the identities
   1. u × (v × w) = (u × v) × w
   2. u × 1 = u
   3. 1 × u = u. -/
def monoid_lang : lang := {C := unit, ..magma_lang}

/-- A group is a {×, ⁻¹, 1}-structure which satisfies the identities
 1. u × (v × w) = (u × v) × w
 2. u × 1 = u
 3. 1 × u = u
 4. u × u−1 = 1
 5. u−1 × u = 1 -/
def group_lang : lang := {F := λ n : ℕ, if n = 2 then unit else if n = 1 then unit else empty,
                          ..magma_lang}

/-- A semiring is a {×, +, 0, 1}-structure which satisfies the identities
  1. u + (v + w) = (u + v) + w
  2. u + v = v + u
  3. u + 0 = u
  5. u × (v × w) = (u × v) × w
  6. u × 1 = u, 1 × u = u
  7. u × (v + w) = (u × v) + (u × w)
  8. (v + w) × u = (v × u) + (w × u)-/
def semiring_lang : lang := {F := λ n : ℕ, if n = 2 then fin 2 else empty,
                              C := fin 2, ..magma_lang}

/-- A ring is a {×,+,−,0,1}-structure which satisfies the identities
   1. u + (v + w) = (u + v) + w
   2. u + v = v + u
   3. u + 0 = u
   4. u + (−u) = 0
   5. u × (v × w) = (u × v) × w
   6. u × 1 = u, 1 × u = u
   7. u × (v + w) = (u × v) + (u × w)
   8. (v + w) × u = (v × u) + (w × u)-/
def ring_lang : lang := {F := λ n : ℕ, if n = 2 then fin 2 else if n = 1 then fin 1 else empty,
                          C := fin 2, ..magma_lang}


/-- An ordered ring is a ring along with a binary ordering relation {<}.-/
def ordered_ring_lang : lang := {R := λ n : ℕ, if n=2 then unit else empty,
                                  ..ring_lang}


/-! -----------------------------------------------------------------
-- 2. Structures and Examples
-- ----------------------------------------------------------------/


/-- We now define an L-structure to be interpretations of functions,
 relations and constants. -/
structure struc (L : lang) : Type 1 :=
(univ : Type)                                    -- universe/domain
(F (n : ℕ) (f : L.F n) : vector univ n → univ)  -- interpretation of each function
(R (n : ℕ) (r : L.R n) : set (vector univ n))    -- interpretation of each relation
(C : L.C → univ)                                -- interpretation of each constant


lemma type_is_struc_of_set_lang {A : Type} : struc (set_lang) :=
begin
  fconstructor,
   { exact A },
   { intros _ f,
     cases f},
   { intros _ r,
     cases r},
   { intros c,
     cases c},
 end


lemma type_is_struc_of_ordered_set_lang {A : Type} [has_lt A]:
  struc (ordered_set_lang) :=
begin
  fconstructor,
   { exact A},
   { intros _ f,
     cases f},
   { intros n r v,
     cases n,
      { cases r}, -- if n=0
     cases n,
      { cases r}, -- if n=1
     cases n; cases r,
      { exact v.nth 0 < v.nth 1} -- if n=2
   },  -- if n>2, handles automatically by Lean.
   { intros c,
     cases c},

end


/-- We need to define a magma, because it looks like it is not defined
  in Mathlib.-/
class magma (α : Type) :=
(mul : α → α → α)


lemma magma_is_struc_of_magma_lang {A : Type} [magma A] :
  struc (magma_lang) :=
begin
  fconstructor,
    { exact A },
    { intros n f v,
      cases n,
      { cases f},                             -- if n = 0
      { exact magma.mul (v.nth 0) (v.nth 1)}}, -- if n = 1
    { intros _ r,
      cases r},
    { intros c,
      cases c},
end



lemma semigroup_is_struc_of_semigroup_lang {A : Type} [semigroup A] :
  struc (semigroup_lang) :=
begin
  fconstructor,
    { exact A},
    { intros n f v,
      cases n,
      cases f,
      exact semigroup.mul (v.nth 0) (v.nth 1)},
    { intros _ r,
      cases r },
    { intro c,
      cases c}
end


lemma monoid_is_struc_of_monoid_lang {A : Type} [monoid A] :
  struc (monoid_lang) := 
begin
  fconstructor,
  { exact A},
  { intros n f v,
    cases n,
    cases f,
    exact monoid.mul (v.nth 0) (v.nth 1)},
  { intros _ r,
      cases r },
    { intro c,
      exact 1},
end


lemma group_is_struc_of_group_lang {A : Type} [group A] :
  struc (group_lang) := 
begin
  fconstructor,
  { exact A },
  { intros n f v,
    cases n,
    cases f,
    cases n,
    {exact group.inv (v.nth 0)},
    cases n,
    {exact group.mul (v.nth 0) (v.nth 1)},
    cases f,
  },
  { intros _ r,
      cases r },
    { intro c,
      exact 1},
end

lemma semiring_is_struc_of_semiring_lang {A : Type} [semiring A] :
  struc (semiring_lang) := 
begin
  fconstructor,
  { exact A },
  { intros n f v,
    iterate 2 {cases n, cases f},  
    cases n,
    cases f,
      {exact semiring.mul (v.nth 0) (v.nth 1)},
      {exact semiring.add (v.nth 0) (v.nth 1)},
  },
  { intros n r,
      cases r },
  { 
    intros c,
    cases c,
    exact semiring.zero,
  },
end

lemma ring_is_struc_of_ring_lang {A : Type} [ring A] :
  struc (ring_lang) := 
begin
  fconstructor,
  {exact A},
  { intros n f v,
    cases n,
    cases f,
    cases n,
    cases f,
    exact ring.neg (v.nth 0),
    cases n,
    cases f,
      exact ring.add (v.nth 0) (v.nth 1),
      exact ring.mul (v.nth 0) (v.nth 1),
  },
  { intros n r,
    cases r },
  {
    intros c,
    cases c,
    exact ring.zero,
  },
end
  
lemma ordered_ring_is_struc_of_ordered_ring_lang {A : Type} [ordered_ring A]
  : struc(ordered_ring_lang) := 
begin
  fconstructor,
  { exact A },
  { intros n f v,
    cases n,
    cases f,
    cases n,
    cases f,
    exact ordered_ring.neg (v.nth 0),
    cases n,
    cases f,
      exact ordered_ring.add (v.nth 0) (v.nth 1),
      exact ordered_ring.mul (v.nth 0) (v.nth 1),
  },
  { intros n r v,
    cases n, 
    cases r,
    cases n,
    cases r,
      exact ordered_ring.lt (v.nth 0) (v.nth 1),
  },
  {
    intros c,
    cases c,
    exact ordered_ring.zero,
  },
end



/-! -----------------------------------------------------------------
-- 3. Embeddings between Structures
-- ----------------------------------------------------------------/


/-- An L-embedding is a map between two L-structures that is injective
on the domain and preserves the interpretation of all the symbols of L.-/
structure embedding {L : lang} (M N : struc L) : Type :=
(η : M.univ → N.univ)                         -- map of underlying domains
(η_inj : function.injective η)                 -- should be one-to-one
(η_F : ∀ n f v,                                -- preserves action of each function
     η (M.F n f v) = N.F n f (vector.map η v))
(η_R : ∀ n r v,                                -- preserves each relation
     v ∈ (M.R n r) ↔ (vector.map η v) ∈ (N.R n r))
(η_C : ∀ c,                                    -- preserves each constant
     η (M.C c) = N.C c)


/-- A bijective L-embedding is called an L-isomorphism.-/
structure isomorphism {L: lang} (M N : struc L) extends (embedding M N) : Type :=
(η_bij : function.bijective η)


/-- The cardinality of a struc is the cardinality of its domain.-/
def card {L : lang} (M : struc L) : cardinal := cardinal.mk M.univ


/-- If η: M → N is an embedding, then the cardinality of N is at least
  the cardinality of M.-/
lemma le_card_of_embedding {L : lang} (M N : struc L) (η : embedding M N) :
  card M ≤ card N :=
begin
  sorry  -- Look for a theorem in mathlib that guarantees the result
         -- using injectivity of η.
end


/-! -----------------------------------------------------------------
-- 4. Terms
-- ----------------------------------------------------------------/


/-- We need a type to represent variables.-/
constant var : Type

#lint
