import tactic
import data.real.basic
import set_theory.cardinal
import data.nat.prime data.stream

/-!
# model.lean

In this file, we define
- functions of arity `(n : ℕ)` and their API.
- languages
- structures
- embedding between two structures on the same language.
- terms
  - we define a function for term substitution and prove a theorem.
  - we give an interpretation of terms in structures.
- formulas.

## Tags

model theory, o-minimality
-/


/-! ## Arity n Functions and their API -/

/-- Inductively define a function on n arguments. 0-arity functions are just
terms of type α.-/
@[reducible] def Func (α : Type) : ℕ → Type
| 0 := α
| (n+1) := α → Func n



/-- Create a type of all functions with finite arity. Here we use Σ to
sum up the types. Sum for types corresponds to union for sets.-/
def Funcs (α : Type) : Type := Σ (n : ℕ), Func α n

/-- If α is inhabited (i.e. if it has at least one term), then so is Funcs α.
This serves 2 purposes:
1. It is good practice to follow each new type definition with an inhabited
   instance. This is to convince us that our defintion makes actual sense and
   that we are not making claims about the empty set.
2. Declaring that type α has an inhabited instance lets us access that term
   by calling it using `arbitrary α` or `default α` anywhere in later proofs
   when an arbitrary α term is needed.

We show that (Funcs α) is inhabited by constructing a 0-level Func
that returns an arbitrary α. -/
instance Funcs.inhabited {α : Type} [inhabited α] : inhabited (Funcs α) :=
 {default := ⟨0, default α⟩}


/-- Define a constructor for Func. It takes in a total function `f` and turns
it into a partial function of the same arity.

1. This constructor can only make functions of arity ≥ 1.
2. This constructor makes a recursive call to itself. -/
def mk_Func_of_total {α : Type} : Π {n : ℕ+}, (vector α n → α) → Func α n
| ⟨0, _⟩ f := by linarith
| ⟨1, _⟩ f := λ a, f ⟨[a], by norm_num⟩ -- this produces a 1-ary func
| ⟨n+2, h⟩ f := λ a, @mk_Func_of_total ⟨n+1, by linarith⟩ (λ v, f (a ::ᵥ v)) -- an (n+1)-ary function


/-- We can apply a Func to an element. This will give us a lower-level
function.

**Deprecation warning**: this function will be removed from future iterations.-/
def app_elem {α : Type} {n : ℕ+} (f : Func α (n+1)) (a : α) : Func α n := f a


/-- A Func can be applied to a vector of elements of the right size.
1. In the base case, apply a 1-ary function to a single element to yield the
   image under said 1-ary function.
2. In the recursive case, we can apply an (n+2)-ary function to (n+2) elements
   by applying it to the head and then recursively calling the result on the
   remaining (n+1)-sized tail. -/
def app_vec {α : Type} : Π {n : ℕ+}, Func α n → vector α n → α
| ⟨0, _⟩   f v := by linarith
| ⟨1, _⟩   f v := f v.head
| ⟨n+2, _⟩ f v := @app_vec ⟨n+1, by linarith⟩ (f v.head) (v.tail)

-- Under this notation, if `(f : Func α n)` and `(v : vector α n)`, then `(f ⊗
-- n)` denotes the value in `α` obtained by feeding the `n` elements of `v` to
-- `f`.
local infix `⊗` : 70 := app_vec


/-- Apply a Func to a function on `fin n`.-/
def app_fin {α : Type} {n : ℕ+} (f : Func α n) (v : fin n → α) : α :=
  f ⊗ (vector.of_fn v)


def Func.map {n : ℕ+} {α : Type} {A : set α} (F : Func α n) {f : A → α} :
 (∀ v : vector A n, F ⊗ v.map f ∈ A) → Func A n :=
 λ h, mk_Func_of_total (λ v, ⟨F ⊗ (v.map f), h v⟩)

/-- We can apply a Func to a vector of elements of the incorrect size as well.-/
def app_vec_partial {α : Type} : Π (m n : ℕ), 0 < m → 0 < n →
  m ≤ n → Func α n → vector α m → Func α (n-m)
| 0     _     _  _  _ _ _ := by linarith
| _     0     _  _  _ _ _ := by linarith
| 1     1     _  _  _ f v := f v.head
| (m+2) 1     h₁ h₂ h f v := by linarith
| 1     (n+2) h₁ h₂ h f v := f v.head
| (m+2) (n+2) _  _  _ f v := by
    { simp only [nat.succ_sub_succ_eq_sub] at *,
      have recursive_call :=
         app_vec_partial (m+1) (n+1) (by norm_num) (by norm_num) (by linarith)
                          (f v.head) v.tail,
      simp only [nat.succ_sub_succ_eq_sub] at recursive_call,
      exact recursive_call,
    }


/-! ## Languages -/

/-- A language is given by specifying functions, relations and constants
along with the arity of each function and each relation.-/
structure lang : Type 1 :=
(F : ℕ+ → Type)    -- functions. ℕ keeps track of arity.
(R : ℕ+ → Type)    -- relations
(C : Type)         -- constants



/-- A dense linear ordering without endpoints is a language containg a
    single binary relation symbol ≤ satisfying the following sentences:
-- 1. ∀x x ≤ x;
-- 2. ∀x ∀y ∀z (x ≤ y → (y ≤ z → x ≤ z));
-- 3. ∀x ∀y (x ≤ y ∨ x = y ∨ y ≤ x);
-- 4. ∀x ∃y x ≤ y;
-- 5. ∀x ∃y y ≤ x;
-- 6. ∀x ∀y (x ≤ y → ∃z (x ≤ z ∧ z ≤ y)).

The  language contains exactly one relation: ≤, and no functions or constants-/
def DLO_lang : lang := {R := λ n : ℕ+,
                        if n = 2 then unit else empty,  -- one binary relation
                        F := function.const ℕ+ empty,   -- no functions
                        C := empty}                     -- no constants

/-- Having defined a DLO_lang, we now use it to declare that lang is an
inhabited type.-/
instance lang.inhabited : inhabited lang := {default := DLO_lang}


def lang.card (L : lang) : cardinal :=
  cardinal.sum (cardinal.mk ∘ L.F) + cardinal.sum (cardinal.mk ∘ L.R)


/-! ## Structures -/


/-- We now define an L-structure to be mapping of functions, relations and
 constants to appropriate elements of a domain/universe type.-/
structure struc (L : lang) : Type 1 :=
(univ : Type)                                   -- universe/domain
(F {n : ℕ+} (f : L.F n) : Func univ n)          -- interpretation of each function
(R {n : ℕ+} (r : L.R n) : set (vector univ n))  -- interpretation of each relation
(C : L.C → univ)                                -- interpretation of each constant


instance struc.inhabited {L : lang} : inhabited (struc L) :=
  {default := {univ := unit,  -- The domain must have at least one term
               F := λ _ _, mk_Func_of_total (function.const _ unit.star),
               R := λ _ _, ∅,
               C := function.const L.C unit.star}
  }


local notation f^M := M.F f -- f^M denotes the interpretation of f in M.
local notation r`̂`M : 150 := M.R r -- r̂M denotes the interpretation of r in
                                 -- M. (type as a variant of \^)


def struc.card {L : lang} (M : struc L) : cardinal := cardinal.mk M.univ

/-! ## Embeddings between Structures -/


/-- An L-embedding is a map between two L-structures that is injective
on the domain and preserves the interpretation of all the symbols of L.-/
structure embedding {L : lang} (M N : struc L) : Type :=
(η : M.univ → N.univ)                        -- map of underlying domains
(η_inj : function.injective η)               -- should be one-to-one
(η_F : ∀ n (f : L.F n) (v : vector M.univ n),
     η (f^M ⊗ v) = f^N ⊗ vector.map η v)    -- preserves action of each function
(η_R : ∀ n (r : L.R n) (v : vector M.univ n),
     v ∈ (r̂M) ↔ (vector.map η v) ∈ (r̂N))   -- preserves each relation
(η_C : ∀ c, η (M.C c) = N.C c)               -- preserves constants



/-- We argue that every structure has an embedding, namely, the embedding
to itself via the identity map.-/
instance embedding.inhabited {L : lang} {M : struc L} : inhabited (embedding M M) :=
  {default := {η := id,
               η_inj := function.injective_id,
               η_F := by simp,
               η_R := by simp,
               η_C := λ _, rfl}}


/-- A bijective embedding between two `L`-structures is called an isomorphism.-/
structure isomorphism {L: lang} (M N : struc L) extends (embedding M N) : Type :=
(η_bij : function.bijective η)


/-- We argue that every structure has an isomorphism to itself via the identity
  map.-/
instance isomorphism.inhabited {L : lang} {M : struc L} : inhabited (isomorphism M M) :=
  {default := {η_bij := function.bijective_id,
               .. default (embedding M M)}}


/-- The cardinality of a structure is the cardinality of its domain.-/
def card {L : lang} (M : struc L) : cardinal := cardinal.mk M.univ



/-- If η: M → N is an embedding, then the cardinality of N is at least the
  cardinality of M.-/
lemma le_card_of_embedding {L : lang} (M N : struc L) (η : embedding M N) :
  card M ≤ card N := cardinal.mk_le_of_injective η.η_inj



/-- If `M ⊆ N` and the inclusion map is an `L`-embedding, we say either
  that `M` is a substructure of `N` or that `N` is an extension of `M`.

Note: the other conditions for `η` being an `L`-embedding follow from the
definition of `coe`.
-/
structure substruc {L : lang} (N : struc L) : Type :=
(univ : set N.univ)              -- a subset of N.univ
(univ_invar_F :  ∀ (n : ℕ+) (f : L.F n) (v : vector univ n),
                 f^N ⊗ (v.map coe) ∈ univ)  -- univ is invariant over f
(univ_invar_C : ∀ (c : L.C), N.C c ∈ univ) -- univ contains all constants


/- TODO : The intersection of 2 structures (on the same language) is a structure.-

Problem: How would we even define the intersection of M.univ and N.univ?
Intersection only makes sense for sets, not types.
-/



/-- A substructure is finite if it has only finitely many domain elements.-/
class fin_substruc {L : lang} {N : struc L} (S : substruc N) :=
(finite : set.finite S.univ)


/-- Every substruc is a struc.-/
instance substruc.has_coe {L: lang} {M : struc L} : has_coe (substruc M) (struc L)
:= {coe := λ (S : substruc M),
           {univ := S.univ,
              F := λ n f, (f^M).map (S.univ_invar_F n f),
              R := λ _ r v, v.map coe ∈ (r̂M),
              C := λ c, ⟨M.C c, S.univ_invar_C c⟩}}


/-! ## Terms -/

/-- We define terms in a language to be constants, variables, functions or
   functions applied to level-0 terms. Here a (term L n) represents all
   terms of level n. Level 0 terms must be constants, variables, or terms
   of type L.F 0.

TODO: Wait for PR#4406: https://github.com/leanprover-community/mathlib/pull/4406
so we can switch to using finvec.
-/
inductive term (L : lang) : ℕ → Type
| con : L.C → term 0
| var : ℕ → term 0
| func {n : ℕ+} : L.F n → term n
| app {n : ℕ} : term (n+1) → term 0 → term n
open term



variables {L : lang} {M : struc L}


/-- This function computes the depth of a term as seen by a parser. For
    example, the depth of `f(v₁, v₂, v₃)` is 4 (one for `f` and one for
    each variable). The depth of `f(v₁, g(v₂), v₃)` is similarly 5.
-/
def term.depth : Π {n : ℕ}, term L n → ℕ
| 0 (con c)    := 1
| 0 (var v)    := 1
| _ (func f)   := 1
| _ (app t t₀) := t.depth + t₀.depth


/-- Every language L is guaranteed to have a 0-level term because
variable terms can be formed without reference to L. In fact, every
language has countably infinite terms of level 0.
-/
instance term.inhabited : inhabited (term L 0) :=
  {default := var 0}


/- Note about Prod and Sum:
  1. Π denotes Prod of types. Represents ∀ at type level.
     Cartesian product of types
  2. Σ denotes Sum of types. Represents ∃ at type level.
     Disjoint union of types (co-product in category of Set/Types).-/

/-- Variables in a of term returned as a finite set. -/
@[reducible] def vars_in_term : Π {n : ℕ}, term L n → finset ℕ
| 0 (con c)    := ∅
| 0 (var v)    := {v}
| _ (func f)   := ∅
| _ (app t t₀) := vars_in_term t ∪ vars_in_term t₀


/-- The number of variables in a term is computed as the size of
the finset given by vars_in_term. -/
@[reducible] def number_of_vars : Π {n : ℕ}, term L n → ℕ
| 0 (con c)    := 0
| 0 (var v)    := 1
| _ (func f)   := 0
| _ (app t t₀) := number_of_vars t + number_of_vars t₀


/-- Given a variable assignment map, we can define an interpretation of an
`L`-term of level `n` as a function on `M.univ` of arity `n`.-/
def term_interpretation (var_assign : ℕ → M.univ) :
  Π {n : ℕ}, term L n → Func M.univ n
| 0 (con c)    := M.C c
| 0 (var v)    := var_assign v
| _ (func f)   := f^M
| _ (app t t₀) := (term_interpretation t) (term_interpretation t₀)


/- The interpretation of an `L`-term `t` in an `L`-structure `M`, under a
variable assignment map `va : ℕ → M.univ` is denoted `va^^t`.-/
notation t`^^`va : 80 := term_interpretation va t



/-! ## 4.2 Terms Substitution
    -----------------------/

/-- Simple example of a map where we substitute every variable
with exactly one term. A lemma will show if the term is variable
free, then the image of the function is variable free. Can be
generalized to subsitute each variable with its own term. -/
def term_sub (t' : term L 0) : Π n, term L n → term L n
| 0 (con c)    := con c
| 0 (var n)    := t'
| n (func f)   := func f
| n (app t t₀) := app (term_sub (n+1) t) (term_sub 0 t₀)

/--Alternative definition where we only allow the substitution to
occur over only one variable.-/

def term_sub_for_var (t' : term L 0) (k : ℕ) :
  Π n, term L n → term L n
| 0 (con c)    := con c
| 0 (var n)    := if k = n then t' else var n
| n (func f)   := func f
| n (app t t₀) := app (term_sub_for_var (n+1) t) (term_sub_for_var 0 t₀)



/-! ##  Formulas and Sentences -/

inductive formula (L : lang)
| tt : formula
| ff : formula
| eq  : term L 0 → term L 0 → formula
| rel : Π {n : ℕ+}, L.R n → vector (term L 0) n → formula
| neg : formula → formula
| and : formula → formula → formula
| or  : formula → formula → formula
| exi : ℕ → formula → formula    -- ℕ gives us a variable
| all : ℕ → formula → formula    -- ℕ gives us a variable


infix    ` =' ` :  80 := formula.eq
prefix   ` ¬' ` :  60 := formula.neg
infix    ` ∧' ` :  70 := formula.and
infix    ` ∨' ` :  70 := formula.or
notation ` ∃' ` : 110 := formula.exi
notation ` ∀' ` : 110 := formula.all
notation ` ⊤' ` : 110 := formula.tt
notation ` ⊥' ` : 110 := formula.ff

def impl (φ₁ : formula L) (φ₂ : formula L) := ¬'φ₁ ∨' φ₂
infix ` →' ` : 80 := impl

def bicond (φ₁ : formula L) (φ₂ : formula L) := (φ₁ →' φ₂)∧'(φ₂ →' φ₁)
infix ` ↔' ` : 80 := bicond


/-- Helper function for variables from list of terms-/
def vars_in_list : list (term L 0) → finset ℕ
| [] := ∅
| (t :: ts) := vars_in_term t ∪ vars_in_list ts


/-- Extracts set of variables from the formula-/
def vars_in_formula : formula L → finset ℕ
| ⊤'                 := ∅
| ⊥'                 := ∅
| (t₁='t₂)           := vars_in_term t₁ ∪ vars_in_term t₂
| (formula.rel _ ts) := vars_in_list (ts.to_list)
| (¬' ϕ)             := vars_in_formula ϕ
| (ϕ₁ ∧' ϕ₂)         := vars_in_formula ϕ₁ ∪ vars_in_formula ϕ₂
| (ϕ₁ ∨' ϕ₂)         := vars_in_formula ϕ₁ ∪ vars_in_formula ϕ₂
| (∃' v ϕ)           := vars_in_formula ϕ ∪ {v}
| (∀' v ϕ)           := vars_in_formula ϕ ∪ {v}



/-- A variable occurs freely in a formula
    1. if it occurs in the formula, AND
    2. if at least one of its occurrences is outside of a quantification.

    For example, this function returns `false` on input `(var, ϕ)` in any of
    the following scenarios --
    - `var` does not occur in `ϕ` at all.
    - `var` occurs in `ϕ` but only after a quantifier.-/
def var_occurs_freely (var : ℕ) : formula L → Prop
| ⊤'                 := false  -- doesn't occur
| ⊥'                 := false  -- doesn't occur
| (t₁='t₂)           := var ∈ vars_in_term t₁ ∪ vars_in_term t₂ -- check occur
| (formula.rel _ ts) := var ∈ vars_in_list (ts.to_list)         -- check occur
| (¬' ϕ)             := var_occurs_freely ϕ
| (ϕ₁ ∧' ϕ₂)         := var_occurs_freely ϕ₁ ∨ var_occurs_freely ϕ₂
| (ϕ₁ ∨' ϕ₂)         := var_occurs_freely ϕ₁ ∨ var_occurs_freely ϕ₂
| (∃' v ϕ)           := (var ≠ v) ∧ var_occurs_freely ϕ -- check not quantified
| (∀' v ϕ)           := (var ≠ v) ∧ var_occurs_freely ϕ -- check not quantified


/-- A formula in which no variable occurs freely is a sentence.  We create a
    subtype of `L`-formulas that we call `L`-sentences.-/
def sentence (L : lang) : Type :=
  {ϕ : formula L // ∀ var, ¬ var_occurs_freely var ϕ}

variables (ϕ : formula L) (σ: sentence L)

/-- Since sentences are a subtype of formula, we define a coercion map for
    conveniently casting any sentence `σ` to a formula by writing `↑σ`.-/
instance coe_sentence_formula : has_coe (sentence L) (formula L) := ⟨λ σ, σ.val⟩


/-! ## Satisfiability and Models -/

/- Define an expanded language, given a struc M.

Idea: For every element of M.univ, we will add a new constant to the
language.

In Lou's book (more general): we start instead with C ⊂ M.univ, and then add
only elements of C as constants to the language. -/
@[reducible] def expanded_lang (L : lang) (M : struc L) : lang :=
  {C := M.univ ⊕ L.C, .. L}


/-- Define expanded structures. -/
def expanded_struc (L: lang) (M : struc L) : struc (expanded_lang L M) :=
  {C := λ c, sum.cases_on c id M.C,
   .. M}



/-- We define what it means for a formula to be true in an `L`-structure
`M`, or consequently, what it means for a structure `M` to model/satisfy a
formula.-/
def models_formula : (ℕ → M.univ) → formula L →  Prop
| _ ⊤'           := true
| _ ⊥'           := false
| va (t₁ =' t₂)   := (t₁^^va) = (t₂^^va)
| va (formula.rel r ts) := vector.map (^^va) ts ∈ (r̂M)
| va (¬' ϕ)       :=  ¬ models_formula va ϕ
| va (ϕ₁ ∧' ϕ₂)   := models_formula va ϕ₁ ∧ models_formula va ϕ₂
| va (ϕ₁ ∨' ϕ₂)   := models_formula va ϕ₁ ∨ models_formula va ϕ₂
| va (∃' v ϕ)     := ∃ (x : M.univ), let va_updated := function.update va v x in
                                      models_formula va_updated ϕ
| va (∀' v ϕ)     := ∀ (x : M.univ), let va_updated := function.update va v x in
                                      models_formula va_updated ϕ

infix ` ⊨ ` : 100 := models_formula  -- Type this as a variant of \entails.

def models_sentence (M : struc L) (σ : sentence L) : Prop := ∃ va : ℕ → M.univ, va ⊨ σ
notation M` ⊨ `σ : 100 := models_sentence M σ -- Type this as a variant of \entails.

lemma models_formula_or_negation (va : ℕ → M.univ) :
  models_formula va ϕ ∨ models_formula va (¬' ϕ) :=
begin
  by_cases (va ⊨ ϕ),
  repeat {tauto},
end

lemma neg_of_sentece_is_sentence :
   ∀ var, ¬ var_occurs_freely var (¬' (↑σ : formula L)) :=
begin
  intros v,
  unfold var_occurs_freely,
  cases σ,
  exact σ_property v,
end


lemma models_sentence_or_negation (M : struc L) (σ : sentence L) :
  models_sentence M σ ∨ models_sentence M ⟨(¬' ↑σ), by sorry⟩ :=
begin
  sorry,
  --by_cases (va ⊨ ϕ),
  --repeat {tauto},
end


/-- We say that two `L`-structures `M` and `N` are elementarily equivalent
and write `M ≡ N` if : `M ⊨ φ` if and only if `N ⊨ φ` for all `L`-sentences
`φ`.-/
def elementarily_equivalent (M₁ M₂: struc L) : Prop :=
  ∀ (ϕ : sentence L), (M₁ ⊨ ϕ) ↔ M₂ ⊨ ϕ
infix `≡` := elementarily_equivalent


/-- The full theory of `M` is the set of `L`-sentences `φ` such that `M ⊨ φ`.-/
def full_theory (M : struc L) : set (sentence L) := {ϕ : sentence L | M ⊨ ϕ}


/-- `M ≡ N` iff their full theories match.-/
lemma eq_full_theory_iff_elementary_equivalent {M N : struc L} :
      full_theory M = full_theory N ↔ M ≡ N :=
begin
  unfold full_theory,
  unfold elementarily_equivalent,
  split,
  {
    intro h,
    intro σ,
    split,
    {
      intro hm,
      have hs : σ ∈ {ϕ : sentence L | M ⊨ ϕ} := by solve_by_elim,
      rw h at hs,
      have hn : N ⊨ σ := by solve_by_elim,
      exact hn,
    },
    {
      intro hn,
      have hs : σ ∈ {ϕ : sentence L | N ⊨ ϕ} := by solve_by_elim,
      rw← h at hs,
      have hm : M ⊨ σ := by solve_by_elim,
      exact hm,
    },
  },
  {
    intro h,
    finish,
  }
end


-- TODO: Theorem: If two structures are isomorphic then they must satisfy the
-- same theory.  Proof by induction on formulas.
theorem isomorphic_struc_satisfy_same_theory (M₁ M₂ : struc L)
  (η : isomorphism M₁ M₂) (σ : sentence L) : M₁ ⊨ σ → M₂ ⊨ σ :=
begin
  cases σ with ϕ hϕ,
  rintros ⟨va, va_models_ϕ⟩,
  have η_map := η.η,
  use η_map ∘ va,
  unfold_coes at *,
  cases ϕ,
    case formula.tt
    { unfold models_formula},      -- every variable assignment satisfies T'
    case formula.ff
    { unfold models_formula at *,  -- no variable assignment can satisfy ⊥'
      tauto,                       -- thus the hypothesis is impossible
    },
    case formula.eq : t₁ t₂
    { unfold models_formula at *,
      -- Question/TODO: term-interpret of t₁ under (η_map∘va) is same as
      -- term-interpret of t₂ under (η_map∘va). Why? How can we show this?
      sorry},
    case formula.rel : n r vec
    { admit },
    case formula.neg : ϕ
    { admit },
    case formula.and : ϕ₁ ϕ₂
    { admit },
    case formula.or : ϕ₁ ϕ₂
    { admit },
    case formula.exi : x ϕ
    { admit },
    case formula.all : x ϕ
    { admit }
end


def isomorphism_inverse (M N : struc L) [nonempty M.univ] [nonempty N.univ]
  (η : isomorphism M N) : isomorphism N M :=
begin
  let ηi := function.inv_fun η.η,
  fconstructor,
  { fconstructor,
    { exact ηi,
    },
    { apply function.bijective.injective,
      rw function.bijective_iff_has_inverse,
      use η.η,
      split,
      have z := function.left_inverse.comp_eq_id,
      unfold function.left_inverse,
      intro x,

      apply @function.inv_fun_eq,
      use ηi x,


      --refine function.right_inverse.left_inverse _,


    sorry},
  repeat {sorry},
  },

{sorry},
end


/-- The full theory is an isomorphism invariant.-/
theorem full_theory_is_isomorphism_invariant {M N : struc L}
 (η : isomorphism M N) : M ≡ N :=
begin
 unfold elementarily_equivalent,
 intro σ,
 split,
 {
   exact isomorphic_struc_satisfy_same_theory M N η σ,
 },
 {
   sorry,
 }
end


/-- Suppose that s₁ and s₂ are variable assignment functions into a structure M
such that s₁(v) = s₂(v) for every free variable v in the term t.
Then t is interpreted to the same element under both s₁ and s₂. -/
lemma eq_term_interpretation_of_identical_var_assign {L : lang} {M : struc L}
  (s₁ s₂ : ℕ → M.univ) (t : term L 0) (h : ∀ v ∈ vars_in_term t, s₁ v = s₂ v) :
  (t^^s₁) = (t^^s₂) :=
begin
  -- We will proceed with induction on the term t.
  -- First we revert the hypothesis h which has `t` in it.
  -- Without reverting, we will not be able to apply induction on t.
  revert h,
  -- We induct on t and then immediately re-introduce hypothesis h in all cases.
  induction t with c v' n f₀ n t t₀ t_ih t₀_ih; intros h,

  { -- In the case when t is a constant, the result holds definitionally.
    refl},

  { -- In the case when t is a variable v', the result is straigtforward once
    -- we use the hypothesis h.
    apply h,
    simp only [vars_in_term, finset.mem_singleton]},

  { -- In the case when t is a function of arity n, the result is definitionally
    -- true for n zero and nonzero.
    cases n; refl},

  { -- In the case when t is an application, we break it into cases when n is
    -- zero and nonzero.
    cases n;
      -- unfold definitions and use the induction hypotheses.
      unfold term_interpretation;
      rw [t_ih, t₀_ih];
      -- The rest follows from hypothesis h.
      unfold vars_in_term at h;
      intros v hv;
      apply h;
      simp only [finset.mem_union];
      -- Note the use of the tactic combinator below to dismiss all goals
      -- simultaneously.
      {right, assumption} <|> {left, assumption}},
end

/-- Consider the formula `ϕ := (r t₁ ... tₙ)`.
    Suppose that `va₁` and `va₂` are variable assignment functions into a
    structure `M` such that `va₁(var)=va₂(var)` for every variable `var` that
    occurs freely in `ϕ`. Then, the formula is satisfied in `M` under `va₁`
    iff it is also satisfied under `va₂`.
-/
lemma iff_models_formula_relation_of_identical_var_assign
  (n : ℕ+) (r : L.R n) (vec : vector (term L 0) n)
  (va₁ va₂ : ℕ → M.univ)
  (h : ∀ var ∈ vars_in_formula (formula.rel r vec), va₁ var = va₂ var) :
  (va₁ ⊨ (formula.rel r vec)) ↔ (va₂ ⊨ (formula.rel r vec)) :=
begin
  set ϕ : formula L := formula.rel r vec,
  unfold vars_in_formula models_formula at *,

  suffices interpretations_eq : vector.map (^^va₁) vec = vector.map (^^va₂) vec,
  rw interpretations_eq,

  ext1,
  rw [vector.nth_map, vector.nth_map,
       eq_term_interpretation_of_identical_var_assign],

  intros var h₁,
  suffices x : var ∈ vars_in_term (vec.nth m) → var ∈ vars_in_list vec.to_list,
    { apply h,
      apply x,
      exact h₁},
  --suffices y : vars_in_term (vec.nth m) ⊆ vars_in_list vec.to_list, apply y,
  --cases (vec.nth m) with c var',
  --{unfold vars_in_term, tauto},

  --simp,intro h₂, rw h₂,
  sorry,
end


/-- Suppose that va₁ and va₂ are variable assignment functions into a structure M
such that va₁(v) = va₂(v) for every free variable v in the formula ϕ.
Then M ⊨ ϕ[va₁] iff M ⊨ ϕ[va₂]. -/
lemma iff_models_formula_of_identical_var_assign (va₁ va₂ : ℕ → M.univ)
  (ϕ : formula L) (h : ∀ v ∈ vars_in_formula ϕ, va₁ v = va₂ v) :
  (va₁ ⊨ ϕ ↔ va₂ ⊨ ϕ) :=
begin
  induction ϕ with t₁ t₂ n r v ϕ ϕ_ih ϕ₁ ϕ₂ ϕ₁_ih ϕ₂_ih ϕ₁ ϕ₂ ϕ₁_ih ϕ₂_ih n ϕ ϕ_ih n ϕ ϕ_ih,
  refl,
  refl,

  {simp only [models_formula, vars_in_formula, finset.mem_union] at h,

   have h₁ : ∀ v ∈ vars_in_term t₁, va₁ v = va₂ v, sorry,
   have h₂ : ∀ v ∈ vars_in_term t₂, va₁ v = va₂ v, sorry,

   have h₃ := eq_term_interpretation_of_identical_var_assign va₁ va₂ t₁ h₁,
   have h₄ := eq_term_interpretation_of_identical_var_assign va₁ va₂ t₂ h₂,
   sorry},

  {apply iff_models_formula_relation_of_identical_var_assign,
  intros v',
  apply h},

  apply not_congr,
  apply ϕ_ih,
  assumption,

  apply and_congr,
  apply ϕ₁_ih,
  intros v H,
  apply h v,
  unfold vars_in_formula,
  simp,
  left,
  exact H,

  apply ϕ₂_ih,
  intros v H,
  apply h v,
  unfold vars_in_formula,
  simp,
  right,
  exact H,

  apply or_congr,
  apply ϕ₁_ih,
  intros v H,
  apply h v,
  unfold vars_in_formula,
  simp,
  left,
  exact H,

  apply ϕ₂_ih,
  intros v H,
  apply h v,
  unfold vars_in_formula,
  simp,
  right,
  exact H,

  apply exists_congr,
  intros x,
  sorry,

  apply forall_congr,
  intros x,
  fconstructor,

  repeat {sorry},
end


/-- If `σ` is a sentence in the language `L` and `M` is an `L`-structure,
either `M ⊨ σ[s]` for all variable assignments or `M ⊨ σ[s]` for no
variable assignment.-/
lemma models_formula_all_or_none_sentences {L: lang} (M : struc L)
  [inhabited M.univ] (σ : sentence L) :
  xor (∀ va : ℕ → M.univ, va ⊨ σ.val) (∀ va' : ℕ → M.univ, ¬ va' ⊨ σ.val) :=
begin
  unfold xor,
  cases σ with σ₁ σ₂ ,
  simp,
  left,
  split,
  rotate,
  use function.const ℕ (default M.univ),
 cases σ₁,
 repeat {sorry},
end


/-- An `L`-theory `T` is simply a set of `L`-sentences. We say that `M` is
a model of `T` and write `M ⊨ T` if `M ⊨ φ` for all sentences `φ ∈ T`.-/
def theory (L : lang) : Type := set (sentence L)
instance theory.has_mem : has_mem (sentence L) (theory L) := ⟨set.mem⟩


/-- We now define a model to be a structure that models a set of sentences
and show `(ℚ, <)` models the axioms for DLO.-/
structure Model {L : lang} (T : theory L)  :=
(M : struc L)
(satis : ∀ σ ∈ T, M ⊨ σ)

def Model.card {t : theory L} (μ : Model t) : cardinal := μ.M.card



/-- We say that a theory is satisfiable if it has a model.-/
def satisfiable_theory (t : theory L) : Prop := nonempty (Model t)


-- TODO: [Hard] Completeness of the DLO_theory
-- Everything that is true in ℚ can be proved from DLO_axioms.

-- Alternate statement: If something is true for ℚ then it is true for every
-- model for DLO_axioms.  (because they all have the same theory).

-- TODO: Vaught's theorem

-- [This is Hard as well] Alternate Branch of Work: Godel encoding?
-- Map from ℕ to the long strings enconding prime factorization.

-- TODO: Quantifier elimination in DLO_theory
-- TODOs: Definability, o-minimality
-- x<2 in ℝ defines (-∞, 2)
-- x=y in ℝ defines a line at 45 degrees.
-- Non-definable: (ℤ, +). ∃x, x+x=x defines {0}. Cannot define {1}.
-- Is ℤ definable?
-- Are even numbers (ℤ, +) ∃ y, x=y+y → (ℤ, +) is not o-minimal.

/-! ## Definability -/




/-! ## Completeness of Language-/

/-- A set of sentences models something if every model of that theory also
 models it.-/
def logical_consequence (t : theory L) (ϕ : sentence L) : Prop :=
  (∀ A : Model t, A.M ⊨ ϕ)

def proof (t : theory L) (ϕ : sentence L) : Prop := sorry

def proves (t : theory L) (ϕ : sentence L) : Prop := ∃ (p : proof t ϕ), sorry

/-- Coercion over a set.-/
def coeset : set(sentence L) → set(formula L) := set.image coe


-- Every inconsistent theory is complete
def is_consistent_theory (t : theory L) : Prop :=
  ∃ (M : struc L), ∀ (σ ∈ t), M ⊨ σ

/-- A theory is complete if any pair of models satisfies exactly the same
sentences.-/
def is_complete_theory (t : theory L) : Prop :=
  ∀ (A₁ A₂ : Model t), A₁.M ≡ A₂.M


lemma is_consistent_theory_full_theory (M : struc L) :
  is_consistent_theory (full_theory M) := by {use M, tauto}

lemma is_complete_theory_full_theory (M : struc L) :
  is_complete_theory (full_theory M) :=
begin
  unfold is_complete_theory,
  intros A₁ A₂,
  unfold elementarily_equivalent,
  intros σ,
  by_cases (σ ∈ full_theory M),
  have H₁ : A₁.M ⊨ σ := A₁.satis σ h,
  have H₂ : A₂.M ⊨ σ := A₂.satis σ h,
  tauto,

  have va : ℕ → A₁.M.univ := sorry,
  --have H₁ : models_formula va A₁.M (¬' ↑σ) := suggest,
  sorry,
end



-- TODO: Theorem: If two structures are isomorphic then they must satisfy the
-- same theory.  Proof by induction on formulas.
theorem isomorphic_struc_satisfy_same_theory (M₁ M₂ : struc L)
  (η : isomorphism M₁ M₂) (σ : sentence L) : M₁ ⊨ σ → M₂ ⊨ σ :=
begin
  sorry
end


class has_infinite_model (t : theory L) : Type 1 :=
(μ : Model t)
(big : cardinal.omega ≤ μ.card)




/-- Lowenheim-Skolem asserts that for a theory over a language L, if that theory
    has an infinite model, then it has a model for any cardinality greater than
    or equal to |L|-/
axiom LS_Lou (k : cardinal) (h : L.card ≤ k) (t : theory L) [has_infinite_model t]:
  ∃ μ : Model t, μ.card = k


/- A theory is k-categorical if all models of cardinality k are isomorphic as
   structures.-/
def theory_kcategorical (k : cardinal) (t : theory L) :=
  ∀ (M₁ M₂ : Model t), M₁.card = k ∧ M₂.card = k → nonempty (isomorphism M₁.M M₂.M)



/-- If a theory is k-categorical and has an infinite model,
    it is complete.-/
theorem Vaught (k : cardinal) (h : L.card ≤ k) (t : theory L)
  [has_infinite_model t] (hkc : theory_kcategorical k t) : is_complete_theory t :=
begin
  -- Proceed by contradiction.
  -- ∃ σ, two models of T that satisfy σ and ¬σ respectively. Call them M₁ and M₂.
  -- This means M₁ models T∪{σ} and M₂ models T∪{¬σ}.
  -- We get two models M₃ and M₄ of same cardinality due to LS.
  -- M₃ and M₄ both model T.
  -- But by kcategoricity, M₃ and M₄ are isomorphic.
  -- Achieve a contradiction using isomorphic_struc_satisfy_same_theory.

sorry,
end

def extend_struc_by_element : sorry := sorry


def extension_of_isomorphism (t : theory L) (M₁ M₂ : Model t) :
  ∀ (S₁ : substruc M₁.M) (S₂ : substruc M₂.M) [fin_substruc S₁] [fin_substruc S₂]
  (η : isomorphism S₁ S₂),
  ∀ (m : M₁.M.univ), ∃ (m': M₂.M.univ),
  ∃ (η' : extend_struc_by_element S₁ m → extend_struc_by_element S₂ m'),
  η' is_isomorphism ∧ (η' m = m') ∧ (η = η' on S₁)
-- TODO: Show that this is true for DLOs.



/-Completeness and Compactness theorems-/

lemma consequence_if_proves {L : lang} (t : theory L) : ∀ (ϕ : sentence L),
      proves t ϕ → logical_consequence t ϕ :=
  begin
    sorry,
  end

theorem completeness {L : lang} (t : theory L) : ∀ (ϕ : sentence L),
        proves t ϕ ↔ logical_consequence t ϕ :=
  begin
    sorry,
  end

theorem compactness {L : lang} (t : theory L) : ∀ (ϕ : sentence L),
        logical_consequence t ϕ → ∃ (t' ⊂ t), logical_consequence t' ϕ :=
  begin
    sorry,
  end
