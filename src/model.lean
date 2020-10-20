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

def dense_linear_order: lang := {R := λ n : ℕ, if n=2 then unit else empty,
                                  F := function.const ℕ empty, C := empty}

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


--A semigroup is a {×}-structure
def semigroup_lang : lang := { ..magma_lang}

-- A monoid is a {×, 1}-structure 
def monoid_lang : lang := { C := unit, ..semigroup_lang}

-- A group is a {×, ⁻¹, 1}-structure 
def group_functions : ℕ → Type
| 1 := unit   -- one unary function
| 2 := unit   -- one binary function
| _ := empty
def group_lang : lang := {F := group_functions, ..monoid_lang}

-- A semiring is a {×, +, 0, 1}-structure 
def semiring_functions : ℕ → Type
| 2 := bool   -- two binary functions
| _ := empty
def semiring_lang : lang := {F := semiring_functions, C := bool, ..group_lang}

-- A ring is a {×,+,−,0,1}-structure
def ring_functions : ℕ → Type
| 1 := unit   -- one unary function
| 2 := bool   -- two binary functions
| _ := empty
def ring_lang : lang := {F := ring_functions, ..semiring_lang}

-- An ordered ring is a {×,+,−,<,0,1}-structure
def ordered_ring_relations : ℕ → Type
| 2 := unit   -- one binary relation
| _ := empty
def ordered_ring_lang : lang := {R := ordered_ring_relations, ..ring_lang}


/-! -----------------------------------------------------------------
-- 2. Structures and Examples
-- ----------------------------------------------------------------/


/-- We now define an L-structure to be interpretations of functions,
 relations and constants. -/
structure struc (L : lang) : Type 1 :=
(univ : Type)                                    -- universe/domain
(F (n : ℕ) (f : L.F n) : vector univ n → univ)   -- interpretation of each function
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
     iterate 2 {cases n, cases r},                         -- n<2: r n = empty 
     cases n,
      exact v.nth 0 < v.nth 1,                             -- n=2: r n = {<}
      cases r,                                             -- n>2: r n = empty
   },
   { intros c,
     cases c},

end

-- ∈ ℕ 
/-- We need to define a magma, because it looks like it is not defined
  in Mathlib.-/
class magma (α : Type) :=
(mul : α → α → α)

lemma free_magma_is_struc_of_magma_lang {A : Type} [magma A] :
  struc (magma_lang) :=
begin
  fconstructor,
  { exact A},
  { 
    intros n f v,
    iterate 2 {cases n, cases f},                          -- n<2 → f n = empty
    cases n,
     exact magma.mul (v.nth 0) (v.nth 1),                  -- n=2 → f n = {×}
     cases f,                                              -- n>2 → f n = empty
  },
  { 
    intros n r,
    cases r 
  },
  { 
    intro c, 
    cases c      -- C = empty
  }
end

lemma semigroup_is_struc_of_semigroup_lang {A : Type} [semigroup A] :
  struc (semigroup_lang) :=
begin
  fconstructor,
  { exact A},
  { 
    intros n f v,
    iterate 2 {cases n, cases f},                          -- n<2 → f n = empty
    cases n,
    { exact semigroup.mul (v.nth 0) (v.nth 1)},            -- n=2 → f n = {×}
    { cases f},                                            -- n>2 → f n empty
  },
  { 
    intros n r,
    cases r 
  },
  { 
    intro c,     -- C = empty
    cases c
  }
end

lemma monoid_is_struc_of_monoid_lang {A : Type} [monoid A] :
  struc (monoid_lang) :=
begin
  fconstructor,
  { exact A},
  { 
    intros n f v,
    iterate 2 {cases n, cases f},                          -- n<2 → f n = empty
    cases n,
    { exact monoid.mul (v.nth 0) (v.nth 1)},               -- n=2 → f n = {×}
    { cases f},                                            -- n>2 → f n = empty
  },
  { 
    intros n r,
    cases r 
  },
  {
    intro c, 
    exact 1,     -- C = {1}
  }
end

lemma group_is_struc_of_group_lang {A : Type} [group A] :
  struc (group_lang) := 
begin
  fconstructor,
  { exact A},
  { 
    intros n f v,
    cases n,
     cases f,                                              -- n=0 → f n = empty
    cases n,
    { exact group.inv (v.nth 0)},                          -- n=1 → f n = {⁻¹}
    cases n,
    { exact group.mul (v.nth 0) (v.nth 1)},                -- n=2 → f n = {×}
    { cases f},                                            -- n>2 → f n = empty
  },
  { 
    intros n r,
    cases r 
  },
  { 
    intro c,
    exact 1,     -- C = {1}
  }
end

lemma semiring_is_struc_of_semiring_lang {A : Type} [semiring A] :
  struc (semiring_lang) := 
begin
  fconstructor,
  { exact A},
  { 
    intros n f v,
    iterate 2 {cases n, cases f},                          -- n<2: f n = empty
    cases n, 
     cases f,                                              -- n=2: f n = {×, +}
     { exact semiring.mul (v.nth 0) (v.nth 1)},            -- × 
     { exact semiring.add (v.nth 0) (v.nth 1)},            -- +
     cases f,                                              -- n>2: f n = empty
  },
  { 
    intros n r,
    cases r 
  },
  {
    intro c,
    cases c,     -- C = {0, 1}
    { exact 0},
    { exact 1}
  }
end

lemma ring_is_struc_of_ring_lang {A : Type} [ring A] :
  struc (ring_lang) := 
begin
  fconstructor,
  { exact A},
  { 
    intros n f v,
    cases n,
     cases f,                                              -- n=0: f n = empty
    cases n,
     exact ring.neg (v.nth 0),                             -- n=1: f n = {-}
    cases n, 
     cases f,                                              -- n=2: f n = {×, +}
     { exact ring.mul (v.nth 0) (v.nth 1)},                -- × 
     { exact ring.add (v.nth 0) (v.nth 1)},                -- +
     cases f,                                              -- n>2: f n = empty
  },
  { 
    intros n r,
    cases r 
  },
  {
    intro c,
    cases c,     --C = {0, 1}
    { exact 0},
    { exact 1}
  }
end

lemma ordered_ring_is_struc_of_ordered_ring_lang {A : Type} [ordered_ring A] :
  struc (ordered_ring_lang) :=
begin
  fconstructor,
  { exact A},
  { 
    intros n f v,
    cases n,
     cases f,                                              -- n=0: f n = empty
    cases n,
     exact ordered_ring.neg (v.nth 0),                     -- n=1: f n = {-}
    cases n, 
     cases f,                                              -- n=2: f n = {×, +}
     { exact ordered_ring.mul (v.nth 0) (v.nth 1)},        -- × 
     { exact ordered_ring.add (v.nth 0) (v.nth 1)},        -- +
     cases f,                                              -- n>2: f n = empty
  },
  {
    intros n r v,
    iterate 2 {cases n, cases r},                          -- n<2: r n = empty
    cases n,
     exact ordered_ring.lt (v.nth 0) (v.nth 1),            -- n=2: r n = {<}
     cases r,                                              -- n>2: r n = empty
  },
  {
    intro c,
    cases c,     --C = {0, 1}
    { exact 0},
    { exact 1}
  }
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
  apply cardinal.mk_le_of_injective,
  exact η.η_inj,
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

def vars_in_formula (f : formula L) : finset ℕ := sorry
def term_interpretation' (M : struc L) (t : term L)
   (v : finset ℕ := vars_in_term_t t)  -- finset of vars in t
   (a : vector M.univ v.card) : M.univ := sorry

def formula_interpretation' (M : struc L) (f : formula L) (v : finset ℕ := vars_in_formula f)  -- finset of vars in f
   (a : vector M.univ v.card) : bool := sorry
    
def is_definable (L : lang) (M : struc L) (X : set M.univ) : Prop := sorry

-- also needs to extend dense linear order (more relations than just <) ?
-- sublanguages

def is_o_minimal (M : struc dense_linear_order) : Prop :=
{
  ∀ X : set M.univ, is_definable dense_linear_order M X →
  ∃n : ℕ, ∃ v : vector (M.univ × M.univ) n, ∃ X₀ : finset M.univ, 
  let S : list (set M.univ) := sorry /- the list of all n open intervals in v -/ in 
  X = sorry -- union of X₀ and each open interval in the list S
}

#check @list.foldr
#check @set.Union 