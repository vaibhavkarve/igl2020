import tactic
import data.real.basic
import set_theory.cardinal
/-!
1. We define languages and give examples.
2. We define structures and give examples.
3. We define embedding between two structures on the same language.
4. We define terms.
   4.1 We give some examples of terms.
   4.2 (WIP) We define a function for term substitution and prove a theorem.
   4.3 (WIP) We give an interpretation of terms in structures.
5. (WIP) We define formulas.
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
                          .. set_lang}


/-- A semigroup is a {×}-structure which satisfies the identity
  u × (v × w) = (u × v) × w.  Note that identities are not relations!-/
def semigroup_lang : lang := magma_lang

/-- A monoid is a {×, 1}-structure which satisfies the identities
   1. u × (v × w) = (u × v) × w
   2. u × 1 = u
   3. 1 × u = u. -/
def monoid_lang : lang := {F := λ n : ℕ, if n=2 then unit else empty,
                           R := function.const ℕ empty,
                           C := unit}

/-- A group is a {×, ⁻¹, 1}-structure which satisfies the identities
 1. u × (v × w) = (u × v) × w
 2. u × 1 = u
 3. 1 × u = u
 4. u × u−1 = 1
 5. u−1 × u = 1 -/
def group_lang : lang := {F := λ n : ℕ, if n=1 then unit else if n=2 then unit else empty,
                          R := λ n : ℕ, empty,
                          C := unit}

/-- A semiring is a {×, +, 0, 1}-structure which satisfies the identities
  1. u + (v + w) = (u + v) + w
  2. u + v = v + u
  3. u + 0 = u
  5. u × (v × w) = (u × v) × w
  6. u × 1 = u, 1 × u = u
  7. u × (v + w) = (u × v) + (u × w)
  8. (v + w) × u = (v × u) + (w × u)-/
def semiring_lang : lang := {F := λ n : ℕ, if n=2 then fin 2 else empty,
                             R := λ n : ℕ, empty,
                             C := fin 2}

/-- A ring is a {×,+,−,0,1}-structure which satisfies the identities
   1. u + (v + w) = (u + v) + w
   2. u + v = v + u
   3. u + 0 = u
   4. u + (−u) = 0
   5. u × (v × w) = (u × v) × w
   6. u × 1 = u, 1 × u = u
   7. u × (v + w) = (u × v) + (u × w)
   8. (v + w) × u = (v × u) + (w × u)-/
def ring_lang : lang := {F := λ n, if n=2 then fin 3 else empty,
                         R := λ n, empty,
                         C := fin 2}

/-- An ordered ring is a ring along with a binary ordering relation {<}.-/
def ordered_ring_lang : lang := {R := λ n, if n=2 then unit else empty,
                                 .. ring_lang}


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

/-- Type is a structure of the set language-/
def type_is_struc_of_set_lang {A : Type} : struc (set_lang) :=
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

/-- Type is a structure of the ordered set language-/
def type_is_struc_of_ordered_set_lang {A : Type} [has_lt A]:
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

/-- Magma is a structure of the magma language-/
def magma_is_struc_of_magma_lang {A : Type} [magma A] :
  struc (magma_lang) :=
begin
  fconstructor,
    { exact A },
    { intros n f v,
      cases n,
      { cases f },                             -- if n = 0
      { exact magma.mul (v.nth 0) (v.nth 1)} }, -- if n = 1
    { intros _ r,
      cases r},
    { intros c,
      cases c},
end

/-- Semigroup is a structure of the language of semigroups-/
def semigroup_is_struc_of_semigroup_lang {A : Type} [semigroup A] :
  struc (semigroup_lang) :=
begin
  fconstructor,
    { exact A },
    { intros n f v,
      cases n,
      cases f,
      exact semigroup.mul (v.nth 0) (v.nth 1)},
    { intros _ r,
      cases r },
    { intro c,
      cases c }
end

/-- Monoid is a structure of the language of monoids-/
def monoid_is_struc_of_monoid_lang {A : Type} [monoid A] :
  struc (monoid_lang) := 
begin
  fconstructor,
  { exact A },
  { intros n f v,
    cases n,
    cases f,
    exact monoid.mul (v.nth 0) (v.nth 1)},
  { intros _ r,
      cases r },
  { intro c,
    exact 1 },
end

/-- Group is a structure of the group language-/
def group_is_struc_of_group_lang {A : Type} [group A] :
  struc (group_lang) := sorry

/-- Semiring is a structure of the language of semirings-/
def semiring_is_struc_of_semiring_lang {A : Type} [semiring A] :
  struc (semiring_lang) := sorry

/-- Ring is a structure of the language of rings-/
def ring_is_struc_of_ring_lang {A : Type} [ring A] :
  struc (ring_lang) := sorry
  
/-- Ordered ring is a structure of the language of ordered rings-/
def ordered_ring_is_struc_of_ordered_ring_lang {A : Type} [ordered_ring A]
  : struc(ordered_ring_lang) := sorry



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
  apply cardinal.mk_le_of_injective,  -- Look for a theorem in mathlib that guarantees the result
  apply η.η_inj,                                    -- using injectivity of η.
end

/-! -----------------------------------------------------------------
-- 4. Terms
-- ----------------------------------------------------------------/

/-- We define terms in a language to be constants, variables or
   applications of functions acting on terms.-/
inductive term (L : lang) : Type
| con : L.C → term
| var : ℕ → term
| app (n : ℕ) (f : L.F n) (ts : list term) : term


open term
variable {L : lang}

mutual def is_admissible, is_admissible_list
with is_admissible : term L → Prop
| (con c) := true
| (var v) := true
| (app n f ts) := (n = ts.length) ∧ is_admissible_list ts
with is_admissible_list : list (term L) → Prop
| [] := true
| (t :: ts) := is_admissible t ∧ is_admissible_list ts

def aterm (L : lang) : Type := {t : term L // is_admissible t}


/-- We define a function to compute the number of variables in a term
using mutual recursion.

Important note: this function counts the number of variables with repetition.
For number without repetition, use the size of the set computed by vars_in_term instead.
-/

mutual def number_of_vars_t, number_of_vars_list_t
with number_of_vars_t : term L → ℕ
| (con c) := 0
| (var v) := 1
| (app n f ts) := number_of_vars_list_t ts
with number_of_vars_list_t : list (term L) → ℕ
| [] := 0
| (t :: ts) := number_of_vars_t t + number_of_vars_list_t ts

def number_of_vars (t : aterm L) : ℕ := number_of_vars_t t.val

/-- The variables in a term can also be computed using a mutually
recursive pair of functions.-/

mutual def vars_in_term_t, vars_in_term_list_t
with vars_in_term_t : term L → finset ℕ
| (con c)      := ∅
| (var v)      := {v}
| (app n f ts) := vars_in_term_list_t ts
with vars_in_term_list_t : list (term L) → finset ℕ
| [] := ∅
| (t :: ts) := vars_in_term_t t ∪ vars_in_term_list_t ts

def vars_in_term (t : aterm L) : finset ℕ := vars_in_term_t t.val



/-! 4.1 Examples of Terms
    ---------------------
The following example is taken from [Marker2002]. -/

namespace example_terms
  /-- The language L has:
  - one unary function f,
  - one binary function g,
  - and one constant symbol c.-/
  def L1 : lang := {F := λ n, if n=1 then unit else if n=2 then unit else empty,
                   R := function.const ℕ empty,
                   C := unit}
  def f : L1.F 1 := unit.star
  def g : L1.F 2 := unit.star
  def c : L1.C   := unit.star

  /-- t₁ = f(g(c, f(v₁))) is a term on language L1. -/
  def t₁ : term L1 := app _ f [app _ g [con c, app _ f [var 1]]]

  
  #eval number_of_vars_t t₁
  #eval vars_in_term_t t₁

end example_terms


/-! 4.2 Terms Substitution
    -----------------------/

/-- Simple example of a map where we substitute every variable
with exactly one term. A lemma will show if the term is variable
free, then the image of the function is variable free. Can be
generalized to subsitute each variable with its own term. -/
mutual def term_sub, term_sub_list (t' : term L)
with term_sub : term L → term L
| (con c)      := con c
| (var n)      := t'
| (app n f ts) := app n f (term_sub_list ts)
with term_sub_list : list (term L) → list (term L)
| [] := []
| (t :: ts) := term_sub t :: term_sub_list ts


def var_free (t : term L) : Prop := number_of_vars_t t = 0


theorem term_sub_free (t' t : term L)
  : var_free t' → var_free (term_sub t' t) :=
begin
  sorry 
end


/-! 4.2 Term Interpretation
    -----------------------
We define an interpretation for L-terms in an L-structure.
This section is a work in progress.
-/
def term_interpretation (M : struc L) (t : term L)
   (v : finset ℕ := vars_in_term_t t)  -- finset of vars in t
   (a : vector M.univ v.card) : M.univ :=
match t with
| (con c)   := M.C c
| (var n)   := begin
                 have h : n ∈ v, sorry,
                 --exact a.nth ⟨v.index_of n, list.index_of_lt_length.2 h⟩,
                 sorry,
               end
| (app n f ts) := sorry
end




/-! -----------------------------------------------------------------
-- 5. Formulas
-- ----------------------------------------------------------------/


inductive formula (L : lang)
| eq  : term L → term L → formula
| rel : Π {n : ℕ}, L.R n → vector (term L) n → formula
| neg : formula → formula
| and : formula → formula → formula
| or  : formula → formula → formula
| exi : ℕ → formula → formula    -- ℕ gives us a variable
| all : ℕ → formula → formula    -- ℕ gives us a variable


infix    `='` :  80 := formula.eq
prefix   `¬'` :  60 := formula.neg
infix    `∧'` :  70 := formula.and
infix    `∨'` :  70 := formula.or
notation `∃'` : 110 := formula.exi
notation `∀'` : 110 := formula.all

/-- A variable occurs freely in a formula if it is not quantified
over.-/
def var_is_free (n : ℕ) : formula L → Prop
| (t₁='t₂)           := true
| (formula.rel r ts) := true
| (¬' ϕ)       := var_is_free ϕ
| (ϕ₁ ∧' ϕ₂)  := var_is_free ϕ₁ ∧ var_is_free ϕ₂
| (ϕ₁ ∨' ϕ₂)  := var_is_free ϕ₁ ∧ var_is_free ϕ₂
| (∃' v ϕ)    := v ≠ n ∧ var_is_free ϕ
| (∀' v ϕ)    := v ≠ n ∧ var_is_free ϕ

/-- If the variable does not occur freely, we say that it is bound.-/
def var_is_bound (n : ℕ) (ϕ : formula L) : Prop := ¬ var_is_free n ϕ

-- TODO: there is some caveat about a variable appearing freely in ϕ₁
-- but bound in ϕ₂ when considering the term ϕ₁ ∧ ϕ₂?

#lint
