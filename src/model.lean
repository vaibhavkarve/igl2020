import tactic
import data.real.basic
import set_theory.cardinal
/-!
0. We define functions of arity (n : ℕ) and their API.
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
-- 0. Arity n Functions and their API
-- ----------------------------------------------------------------/

/-- Inductively define a function on n arguments. 0-arity functions are just
terms of type α.-/
@[reducible] def Func (α : Type) : ℕ → Type
| 0 := α
| (nat.succ n) := α → Func n

/-- Create a type of ALL functions with finite arity. Here we use Σ to
sum up the types. Sum for types :: union for sets.-/
def Funcs (α : Type) : Type := Σ (n : ℕ), Func α n

/-- We can apply a Func to an element. This will give us a lower-level
function.-/
def app_elem {α : Type} {n : ℕ} (f : Func α n) (h : 0 < n) (a : α) : Func α (n-1) :=
begin
 cases n,
    linarith,  -- Rule out case (n=0) because n assumed positive
  exact f a,
end


/-- We can apply a Func to a vector of elements of the right size.-/
def app_vec {α : Type} {n : ℕ} (f : Func α n) (v : vector α n) : α :=
begin
  induction n with n n_ih,
   { exact f},
  apply n_ih,
  exact app_elem f (by norm_num) v.head,  -- apply f to the first element of v
  exact v.tail,                            -- recursively apply to the tail of v
end

/-- We can apply a Func to a function on `fin n`.-/
def app_fin {α : Type} {n : ℕ} (f : Func α n) (v : fin n → α) : α :=
  app_vec f (vector.of_fn v)


/-- We can apply a Func to a vector of elements of the incorrect size as well.-/
def app_vec_partial {α : Type} {n m : ℕ} (h : m ≤ n) (f : Func α n)
  (v : vector α m) : Func α (n-m) := sorry



/-! -----------------------------------------------------------------
-- 1. Languages and Examples
-- ----------------------------------------------------------------/

/-- A language is given by specifying functions, relations and constants
along with the arity of each function and each relation.-/
structure lang : Type 1 :=
(F : ℕ → Type)    -- functions. ℕ keeps track of arity.
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
  u × (v × w) = (u × v) × w.  Note that identities are not relations!-/
def semigroup_lang : lang := magma_lang

/-- A monoid is a {×, 1}-structure which satisfies the identities
   1. u × (v × w) = (u × v) × w
   2. u × 1 = u
   3. 1 × u = u. -/
def monoid_lang : lang := {F := λ n : ℕ, if n=2 then unit else empty, 
                            C := unit, ..set_lang}

/-- A group is a {×, ⁻¹, 1}-structure which satisfies the identities
 1. u × (v × w) = (u × v) × w
 2. u × 1 = u
 3. 1 × u = u
 4. u × u−1 = 1
 5. u−1 × u = 1 -/
def group_lang : lang := {F := λ n : ℕ, if n = 2 then unit else if n = 1 then unit else empty,
                          C := unit, ..set_lang}

/-- A semiring is a {×, +, 0, 1}-structure which satisfies the identities
  1. u + (v + w) = (u + v) + w
  2. u + v = v + u
  3. u + 0 = u
  5. u × (v × w) = (u × v) × w
  6. u × 1 = u, 1 × u = u
  7. u × (v + w) = (u × v) + (u × w)
  8. (v + w) × u = (v × u) + (w × u)-/
def semiring_lang : lang := sorry

/-- A ring is a {×,+,−,0,1}-structure which satisfies the identities
   1. u + (v + w) = (u + v) + w
   2. u + v = v + u
   3. u + 0 = u
   4. u + (−u) = 0
   5. u × (v × w) = (u × v) × w
   6. u × 1 = u, 1 × u = u
   7. u × (v + w) = (u × v) + (u × w)
   8. (v + w) × u = (v × u) + (w × u)-/
def ring_lang : lang := sorry

/-- An ordered ring is a ring along with a binary ordering relation {<}.-/
def ordered_ring_lang : lang := sorry


/-! -----------------------------------------------------------------
-- 2. Structures and Examples
-- ----------------------------------------------------------------/


/-- We now define an L-structure to be interpretations of functions,
 relations and constants. -/
structure struc (L : lang) : Type 1 :=
(univ : Type)                                   -- universe/domain
(F (n : ℕ) (f : L.F n) : Func univ n)          -- interpretation of each function
(R (n : ℕ) (r : L.R n) : set (vector univ n))  -- interpretation of each relation
(C : L.C → univ)                               -- interpretation of each constant


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
     iterate {cases n, cases r},
     exact (v.nth 0 < v.nth 1),
     cases r},
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
    { intros n f,
      iterate {cases n, cases f}, -- if n=0,1
      exact magma.mul, -- if n=2
      cases f},        -- if n≥3
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
    { intros n f,
      iterate {cases n, cases f},
      exact semigroup.mul,
      cases f},
    { intros _ r,
      cases r},
    { intro c,
      cases c}
end

/-- Monoid is a structure of the language of monoids-/
def monoid_is_struc_of_monoid_lang {A : Type} [monoid A] :
  struc (monoid_lang) := 
begin
  fconstructor,
  { exact A },
  { intros n f,
    iterate {cases n, cases f},
    exact monoid.mul,
    cases f},
  { intros _ r,
      cases r},
  { intro c,
    exact 1},
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
(η : M.univ → N.univ)                        -- map of underlying domains
(η_inj : function.injective η)                -- should be one-to-one
(η_F : ∀ n f v,                              -- preserves action of each function
     η (app_vec (M.F n f) v) = app_vec (N.F n f) (vector.map η v))
(η_R : ∀ n r v,                              -- preserves each relation
     v ∈ (M.R n r) ↔ (vector.map η v) ∈ (N.R n r))
(η_C : ∀ c,                                   -- preserves each constant
     η (M.C c) = N.C c)


/-- A bijective L-embedding is called an L-isomorphism.-/
structure isomorphism {L: lang} (M N : struc L) extends (embedding M N) : Type :=
(η_bij : function.bijective η)


/-- The cardinality of a struc is the cardinality of its domain.-/
def card {L : lang} (M : struc L) : cardinal := cardinal.mk M.univ


/-- If η: M → N is an embedding, then the cardinality of N is at least
  the cardinality of M.-/
lemma le_card_of_embedding {L : lang} (M N : struc L) (η : embedding M N) :
  card M ≤ card N := cardinal.mk_le_of_injective η.η_inj

/-! -----------------------------------------------------------------
-- 4. Terms
-- ----------------------------------------------------------------/
variables (L : lang) (M : struc L)

/-- We define terms in a language to be constants, variables, functions or
   functions applied to level-0 terms. Here a (term L n) represents all
   terms of level n. Level 0 terms must be constants, variables, or terms
   of type L.F 0.-/
inductive term : ℕ → Type
| con : L.C → term 0
| var : ℕ → term 0
| func {n : ℕ} : L.F n → term n
| app {n : ℕ} : term (n+1) → term 0 → term n
open term

/- Note about Prod and Sum:
  1. Π denotes Prod of types. Represents ∀ at type level.
     Cartesian product of types
  2. Σ denotes Sum of types. Represents ∃ at type level.
     Disjoint union of types (co-product in category of Set/Types).-/

/-- Variables in a term.-/
def vars_in_term {L : lang} : Π {n : ℕ}, term L n → list ℕ
| 0 (con c)    := []
| 0 (var v)    := [v]
| n (func f)   := []
| n (app t t₀) := vars_in_term t ++ vars_in_term t₀

/-- The number of variables in a term. We remove duplicates before
counting.-/
def number_of_vars {L : lang} {n : ℕ} (t : term L n) : ℕ :=
  (vars_in_term t).erase_dup.length


def term_interpretation : Π {n : ℕ}, term L n → Funcs M.univ
| 0 (con c) := ⟨0, M.C c⟩
| 0 (var v) := ⟨1, id⟩
| n (func f) := ⟨n, M.F n f⟩
| n (app t t₀) := sorry


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

  def M1 : struc L1 :=
  {univ := ℝ,
   F := by {intros n f,
            cases n, { cases f},            -- if n=0
            cases n, { exact λ x : ℝ, x*2}, -- if n=1
            cases n, { exact (+)},          -- if n=2
            cases f},                       -- if n>2
   R := λ _ f _, by {cases f},
   C := λ c, 1}


  /-- t₃ = f(g(c, f(v₅))) is a term on language L1.-/
  def t₁ : term L1 0 := app (func f) (var 5)            -- f(v₅)
  def t₂ : term L1 0 := app (app (func g) (con c)) t₁   -- g(c)(t₁)
  def t₃ : term L1 0 := app (func f) t₂                 -- f(t₂)


end example_terms


/-! 4.2 Terms Substitution
    -----------------------/

/-- Simple example of a map where we substitute every variable
with exactly one term. A lemma will show if the term is variable
free, then the image of the function is variable free. Can be
generalized to subsitute each variable with its own term. -/
def term_sub {L : lang} {m : ℕ} (t' : term L m) : Π n, term L n → term L n
| 0 (con c)    := con c
| 0 (var n)    := sorry -- This used to be t'. What should it be now?
| n (func f)   := sorry
| n (app t t₀) := sorry -- This used to be [app n f (term_sub_list ts)].


def var_free {L : lang} {n : ℕ} (t : term L n) : Prop := number_of_vars t = 0


theorem term_sub_free {n m : ℕ} (t' : term L n) (t : term L m)
  : var_free t' → var_free (term_sub t' m t) :=
begin
  sorry 
end



/-! -----------------------------------------------------------------
-- 5. Formulas
-- ----------------------------------------------------------------/


inductive formula (L : lang)
| eq  : Π {n : ℕ}, term L n → term L n → formula
| rel : Π {n : ℕ}, L.R n → vector (term L n) n → formula
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
def var_is_bound (n : ℕ) (ϕ : formula L) : Prop := ¬ var_is_free L n ϕ

-- TODO: there is some caveat about a variable appearing freely in ϕ₁
-- but bound in ϕ₂ when considering the term ϕ₁ ∧ ϕ₂?

