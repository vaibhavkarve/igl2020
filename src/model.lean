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
def mk_Func_of_total {α : Type} : Π {n : ℕ}, (vector α (n+1) → α) → Func α (n+1)
| 0     := λ f a, f ⟨[a], by norm_num⟩                -- this produces a 1-ary func
| (n+1) := λ f a, mk_Func_of_total (λ v, f (a ::ᵥ v))  -- an (n+2)-ary function


/-- We can apply a Func to an element. This will give us a lower-level
function.

**Deprecation warning**: this function will be removed from future iterations.-/
def app_elem {α : Type} {n : ℕ} (f : Func α (n+1)) (a : α) : Func α n := f a


/-- A Func can be applied to a vector of elements of the right size.
1. In the base case, apply a 1-ary function to a single element to yield the
   image under said 1-ary function.
2. In the recursive case, we can apply an (n+2)-ary function to (n+2) elements
   by applying it to the head and then recursively calling the result on the
   remaining (n+1)-sized tail. -/
def app_vec {α : Type} : Π {n : ℕ}, Func α (n+1) → vector α (n+1) → α
| 0     := λ f v, f v.head
| (n+1) := λ f v, app_vec (f v.head) (v.tail)

-- Under this notation, if `(f : Func α n)` and `(v : vector α n)`, then `(f ⊗
-- n)` denotes the value in `α` obtained by feeding the `n` elements of `v` to
-- `f`.
local infix `⊗` : 70 := app_vec


/-- Apply a Func to a function on `fin n`.-/
def app_fin {α : Type} {n : ℕ} (f : Func α (n+1)) (v : fin (n+1) → α) : α :=
  f ⊗ (vector.of_fn v)


/-- We can apply a Func to a vector of elements of the incorrect size as well.
TODO: Turn this into patter-matched term-style definition.
-/
def app_vec_partial {α : Type} {n m : ℕ} (h : m ≤ n) (f : Func α (n+1))
  (v : vector α (m+1)) : Func α (n-m) :=
begin
 induction m with m mih,
   { exact f v.head},
  have nat_ineq : n-m.succ+1 = n-m := by omega,
  have f' : Func α (n-m) := mih (by omega) v.tail,
  rw ← nat_ineq at f',
  exact f' v.head,
end


def app_vec_partial' {α : Type} : Π (m n : ℕ),
  m ≤ n → Func α (n+1) → vector α (m+1) → Func α (n-m)
| 0     0     := λ h f v, f v.head
| (m+1) 0     := sorry
| 0     (n+1) := sorry
| (m+1) (n+1) := sorry
--| (m+1) (n+1) := λ h f v, app_vec_partial' (_ : m ≤ n-1) (f v.head (by omega)) (v.tail)

/-! ## Languages -/

/-- A language is given by specifying functions, relations and constants
along with the arity of each function and each relation.-/
structure lang : Type 1 :=
(F : ℕ → Type)    -- functions. ℕ keeps track of arity.
(R : ℕ → Type)    -- relations

/-- Constants of a language are simply its 0-ary functions. -/
def lang.C (L : lang) : Type := L.F 0


/-- A dense linear ordering without endpoints is a language containg a
    single binary relation symbol ≤ satisfying the following sentences:
-- 1. ∀x x ≤ x;
-- 2. ∀x ∀y ∀z (x ≤ y → (y ≤ z → x ≤ z));
-- 3. ∀x ∀y (x ≤ y ∨ x = y ∨ y ≤ x);
-- 4. ∀x ∃y x ≤ y;
-- 5. ∀x ∃y y ≤ x;
-- 6. ∀x ∀y (x ≤ y → ∃z (x ≤ z ∧ z ≤ y)).

The  language contains exactly one relation: ≤, and no functions or constants-/
def DLO_lang : lang := {R := λ n : ℕ,
                        if n = 2 then unit else empty,  -- one binary relation
                        F := function.const ℕ empty}

/-- Having defined a DLO_lang, we now use it to declare that lang is an
inhabited type.-/
instance lang.inhabited : inhabited lang := {default := DLO_lang}


/-! ## Structures -/


/-- We now define an L-structure to be mapping of functions, relations and
 constants to appropriate elements of a domain/universe type.-/
structure struc (L : lang) : Type 1 :=
(univ : Type)                                   -- universe/domain
(F {n : ℕ} (f : L.F n) : Func univ n)          -- interpretation of each function
(R {n : ℕ} (r : L.R n) : set (vector univ n))  -- interpretation of each relation

def struc.C {L : lang} (M : struc L) : L.C → M.univ := @struc.F L M 0


instance struc.inhabited {L : lang} : inhabited (struc L) :=
  {default := {univ := unit,  -- The domain must have at least one term
               F := λ _ _, mk_Func_of_total (function.const _ unit.star) unit.star,
               R := λ _ _, ∅}
  }


local notation f^M := struc.F M f -- f^M denotes the interpretation of f in M.
local notation r`̂`M : 150 := struc.R M r -- r̂M denotes the interpretation of r in
                                 -- M. (type as a variant of \^)


/-! ## Embeddings between Structures -/


/-- An L-embedding is a map between two L-structures that is injective
on the domain and preserves the interpretation of all the symbols of L.-/
structure embedding {L : lang} (M N : struc L) : Type :=
(η : M.univ → N.univ)                        -- map of underlying domains
(η_inj : function.injective η)               -- should be one-to-one
(η_F : ∀ n (f : L.F (n+1)) (v : vector M.univ (n+1)),
     η (f^M ⊗ v) = f^N ⊗ vector.map η v)    -- preserves action of each function
(η_R : ∀ n (r : L.R (n+1)) (v : vector M.univ (n+1)),
     v ∈ (r̂M) ↔ (vector.map η v) ∈ (r̂N))   -- preserves each relation
(η_C : ∀ c, η (M.C c) = N.C c)               -- preserves constants


@[simp] lemma vec_map_id {α : Type} {n : ℕ} (v : vector α n) : vector.map id v = v :=
begin
  apply vector.eq,
  simp only [list.map_id, vector.to_list_map],
end


/-- We argue that every structure has an L-embedding, namely, the embedding
to itself via the identity map.-/
instance embedding.inhabited {L : lang} {M : struc L} : inhabited (embedding M M) :=
  {default := {η := id,
               η_inj := function.injective_id,
               η_F := by simp,
               η_R := by simp,
               η_C := λ _, rfl}}


/-- A bijective L-embedding is called an L-isomorphism.-/
structure isomorphism {L: lang} (M N : struc L) extends (embedding M N) : Type :=
(η_bij : function.bijective η)


/-- We argue that every structure has an L-isomorphism, namely, the isomorphism
to itself.-/
instance isomorphism.inhabited {L : lang} {M : struc L} : inhabited (isomorphism M M) :=
  {default := {η_bij := function.bijective_id,
               .. default (embedding M M)}}


/-- The cardinality of a struc is the cardinality of its domain.-/
def card {L : lang} (M : struc L) : cardinal := cardinal.mk M.univ


/-- If η: M → N is an embedding, then the cardinality of N is at least
  the cardinality of M.-/
lemma le_card_of_embedding {L : lang} (M N : struc L) (η : embedding M N) :
  card M ≤ card N := cardinal.mk_le_of_injective η.η_inj

/-! ## Terms -/

variables (L : lang) (M : struc L)

/-- We define terms in a language to be constants, variables, functions or
   functions applied to level-0 terms. Here a (term L n) represents all
   terms of level n. Level 0 terms must be constants, variables, or terms
   of type L.F 0.-/
inductive term : ℕ → Type
| con : L.C → term 0
| var : ℕ → term 0
| func {n : ℕ} : L.F n → term n
| app {n : ℕ} : term (n + 1) → term 0 → term (n)
open term


/-- Every language L is guaranteed to have a 0-level term because
variable terms can be formed without reference to L. In fact, every
language has countably infinite terms of level 0.
-/
instance term.inhabited {L : lang} : inhabited (term L 0) :=
  {default := var 0}

/- Note about Prod and Sum:
  1. Π denotes Prod of types. Represents ∀ at type level.
     Cartesian product of types
  2. Σ denotes Sum of types. Represents ∃ at type level.
     Disjoint union of types (co-product in category of Set/Types).-/

/-- Variables in a of term returned as a finite set. -/
@[reducible] def vars_in_term {L : lang} : Π {n : ℕ}, term L n → finset ℕ
| 0 (con c)    := ∅
| 0 (var v)    := {v}
| _ (func f)   := ∅
| _ (app t t₀) := vars_in_term t ∪ vars_in_term t₀


/-- The number of variables in a term is computed as the size of
the finset given by vars_in_term. -/
@[reducible] def number_of_vars {L : lang} : Π {n : ℕ}, term L n → ℕ
| 0 (con c)    := 0
| 0 (var v)    := 1
| _ (func f)   := 0
| _ (app t t₀) := number_of_vars t + number_of_vars t₀


def term_interpretation {L : lang} (M : struc L)(var_assign : ℕ → M.univ) :
  Π {n : ℕ}, term L n →  Func M.univ n
| 0 (con c)    := M.C c
| 0 (var v)    := var_assign v
| n (func f)   := f^M
| n (app t t₀) := (term_interpretation t) (term_interpretation t₀)




/-! ## 4.2 Terms Substitution
    -----------------------/

/-- Simple example of a map where we substitute every variable
with exactly one term. A lemma will show if the term is variable
free, then the image of the function is variable free. Can be
generalized to subsitute each variable with its own term. -/
def term_sub {L : lang} (t' : term L 0) : Π n, term L n → term L n
| 0 (con c)    := con c
| 0 (var n)    := t'
| n (func f)   := func f
| n (app t t₀) := app (term_sub (n+1) t) (term_sub 0 t₀)

/--Alternative definition where we only allow the substitution to
occur over only one variable.-/

def term_sub_for_var {L : lang} (t' : term L 0) (k : ℕ) :
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
| rel : Π (n : ℕ), L.R n → vector (term L 0) n → formula
| neg : formula → formula
| and : formula → formula → formula
| or  : formula → formula → formula
| exi : ℕ → formula → formula    -- ℕ gives us a variable
| all : ℕ → formula → formula    -- ℕ gives us a variable


local infix    `='` :  80 := formula.eq
local prefix   `¬'` :  60 := formula.neg
local infix    `∧'` :  70 := formula.and
local infix    `∨'` :  70 := formula.or
local notation `∃'` : 110 := formula.exi
local notation `∀'` : 110 := formula.all
local notation `⊤'` : 110 := formula.tt
local notation `⊥'` : 110 := formula.ff

def impl {L : lang} (φ₁ : formula L) (φ₂ : formula L) := ¬'φ₁ ∨' φ₂
local infix `→'` : 80 := impl

def bicond {L: lang} (φ₁ : formula L) (φ₂ : formula L) :=
  (φ₁ →' φ₂) ∧' (φ₂ →' φ₁)
infix `↔'` : 80 := bicond



/-- Helper function for variables from list of terms-/
def vars_in_list {L : lang} : list (term L 0) → finset ℕ
|[] := ∅
|(t :: ts) := vars_in_term t ∪ vars_in_list ts


/-- Extracts set of variables from the formula-/
def vars_in_formula {L : lang} : formula L → finset ℕ
| ⊤'                 := ∅
| ⊥'                 := ∅
| (t₁='t₂)           := vars_in_term t₁ ∪ vars_in_term t₂
| (formula.rel _ r ts) := vars_in_list (ts.to_list)
| (¬' ϕ)       := vars_in_formula ϕ
| (ϕ₁ ∧' ϕ₂)  := vars_in_formula ϕ₁ ∪ vars_in_formula ϕ₂
| (ϕ₁ ∨' ϕ₂)  := vars_in_formula ϕ₁ ∪ vars_in_formula ϕ₂
| (∃' v ϕ)    := vars_in_formula ϕ ∪ {v}
| (∀' v ϕ)    := vars_in_formula ϕ ∪ {v}


/-- A variable occurs freely in a formula if it is not quantified
over.-/
def is_var_free (n : ℕ) {L : lang} : formula L → Prop
| ⊤'                 := true
| ⊥'                 := true
| (t₁='t₂)           := true
| (formula.rel _ r ts) := true
| (¬' ϕ)       := is_var_free ϕ
| (ϕ₁ ∧' ϕ₂)  := is_var_free ϕ₁ ∧ is_var_free ϕ₂
| (ϕ₁ ∨' ϕ₂)  := is_var_free ϕ₁ ∧ is_var_free ϕ₂
| (∃' v ϕ)    := v ≠ n ∧ is_var_free ϕ
| (∀' v ϕ)    := v ≠ n ∧ is_var_free ϕ


/-- If the variable does not occur freely, we say that it is bound.-/
def var_is_bound {L : lang} (n : ℕ) (ϕ : formula L) : Prop := ¬ is_var_free n ϕ


/-- We use the following to define sentences within Lean-/
def is_sentence {L : lang} (ϕ : formula L) : Prop :=
  ∀ n : ℕ, (n ∈ vars_in_formula ϕ → var_is_bound n ϕ)

def sentence (L : lang) : Type := {ϕ : formula L // is_sentence ϕ}

/-! ## Examples of formulas and sentences.-/


/-! ## Satisfiability and Models -/

/- Define an expanded language, given a struc M.

Idea: For every element of M.univ, we will add a new constant to the
language.

In Lou's book (more general): we start instead with C ⊂ M.univ, and then add
only elements of C as constants to the language. -/
@[reducible] def expanded_lang (L : lang) (M : struc L) : lang :=
  {F := λ n, if n=0 then M.univ ⊕ L.F 0 else L.F n,
   .. L}


/-- Define expanded structures. -/
def expanded_struc (L: lang) (M : struc L) : struc (expanded_lang L M) :=
  {C := λ c, sum.cases_on c id (M.F 0),
   F := λ n f, by {dsimp only at f,
                   split_ifs at f with h₁ h₂,
                   rw h₁,
                   exact sum.cases_on f id (M.F 0),
                   exact M.F n f},
   .. M}


/-- We now interpret what it means for a formula to be true/modeled in
an L-structure. -/
def models {L : lang} {M : struc L} : (ℕ → M.univ) → formula L →  Prop
| va ⊤'           := true
| va ⊥'           := false
| va (t₁ =' t₂)   := (term_interpretation M va t₁) = (term_interpretation M va t₂)
| va (formula.rel _ r ts) := vector.map (term_interpretation M va) ts ∈ M.R ts.length r
| va ¬' ϕ             :=  ¬ models va ϕ
| va (ϕ₁ ∧' ϕ₂)      := models va (ϕ₁) ∧ models va (ϕ₂)
| va (ϕ₁ ∨' ϕ₂)      := models va (ϕ₁) ∨ models va (ϕ₂)
| va (∃' v ϕ)        := ∃ (x : M.univ), models (λ n, if n=v then x else va n) ϕ
| va (∀' v ϕ)        := ∀ (x : M.univ), models (λ n, if n=v then x else va n) ϕ


/-- Suppose that s₁ and s₂ are variable assignment functions into a structure M
such that s₁(v) = s₂(v) for every free variable v in the term t.
Then t is interpreted to the same element under both s₁ and s₂. -/
lemma eq_term_interpretation_of_identical_var_assign {L : lang} {M : struc L}
  (s₁ s₂ : ℕ → M.univ) (t : term L 0)
  (h : ∀ v ∈ vars_in_term t, s₁ v = s₂ v) :
  (term_interpretation M s₁ t = term_interpretation M s₂ t) :=
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


/-- Suppose that s₁ and s₂ are variable assignment functions into a structure
M such that s₁(v)=s₂(v) for every free variable v. The vector v on n terms is
satisfied in M under s₁ iff it is also satisfied under s₂. -/
lemma iff_models_relation_of_identical_var_assign {L : lang} {M : struc L}
  (n : ℕ)
  (s₁ s₂ : ℕ → M.univ)
  (r : L.R n)
  (vec : vector (term L 0) n)
  (h : ∀ v ∈ vars_in_formula (formula.rel n r vec), s₁ v = s₂ v) :
  models s₁ (formula.rel n r vec) ↔ models s₂ (formula.rel n r vec) :=
begin
  unfold models,
  suffices x : vector.map (term_interpretation M s₁) vec
               = vector.map (term_interpretation M s₂) vec,
  rw x,
  ext1,
  rw [vector.nth_map, vector.nth_map,
       eq_term_interpretation_of_identical_var_assign],

  intros v H,
  apply h,

  unfold vars_in_formula,
  cases n,
   {sorry},  -- this should be the R0 case. Probably can be dismissed by norm_num or linarith


  sorry
end


/-- Suppose that s₁ and s₂ are variable assignment functions into a structure M
such that s₁(v) = s₂(v) for every free variable v in the formula ϕ.
Then M ⊨ ϕ[s₁] iff M ⊨ ϕ[s₂]. -/
lemma iff_models_of_identical_var_assign (s₁ s₂ : ℕ → M.univ) (ϕ : formula L)
  (h : ∀ v ∈ vars_in_formula ϕ, s₁ v = s₂ v) : (models s₁ ϕ ↔ models s₂ ϕ) :=
begin
  induction ϕ with t₁ t₂ n r v ϕ ϕ_ih ϕ₁ ϕ₂ ϕ₁_ih ϕ₂_ih ϕ₁ ϕ₂ ϕ₁_ih ϕ₂_ih n ϕ ϕ_ih n ϕ ϕ_ih,

  refl,
  refl,

  {unfold models,
   simp only [vars_in_formula, finset.mem_union] at h,

   have h₁ : ∀ v ∈ vars_in_term t₁, s₁ v = s₂ v, sorry,
   have h₂ : ∀ v ∈ vars_in_term t₂, s₁ v = s₂ v, sorry,

   have h₃ := eq_term_interpretation_of_identical_var_assign s₁ s₂ t₁ h₁,
   have h₄ := eq_term_interpretation_of_identical_var_assign s₁ s₂ t₂ h₂,
   sorry},

  {apply iff_models_relation_of_identical_var_assign,
  intros v',
  apply h},

  unfold models,
  apply not_congr,
  apply ϕ_ih,
  assumption,

  unfold models,
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

  unfold models,
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

  unfold models,
  apply exists_congr,
  intros x,
  sorry,

  unfold models,
  apply forall_congr,
  intros x,
  sorry,
end


/--If σ is a sentence in the language L and M is an L-structure, either M ⊨ σ[s]
for all assignment functions s, of M ⊨ σ[s] for no assignment function s. -/
lemma models_all_or_none_sentences {L: lang} (M : struc L) [inhabited M.univ] (σ : sentence L) :
  xor (∀ va : ℕ → M.univ, models va σ.val)
      (∀ va' : ℕ → M.univ, ¬ models va' σ.val) :=
begin
  unfold xor,
  cases σ with σ₁ σ₂ ,
  simp,
  left,
  split,
  rotate,
  use function.const ℕ (default M.univ),

 cases σ₁,
 unfold models,
 repeat {sorry},
end

-- TODO: make notation for models : ⊧ or ⊨


/--We now define a model to be a structure that models a set
of sentences and show (ℚ, <) models the axioms for DLO.-/

structure Model {L : lang} (axs : set(formula L)) : Type 1 :=
(M : struc L)
(va : ℕ → M.univ)
(satis : ∀ (σ ∈ axs), models va σ)



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

/- Definability
   ============
-/




/-- Godel Encoding/Numbering
    =======================

Section 5.5 in Lou's notes.
-/

-- Scott is going to attempt the impossible.
def godel_encoding (L : lang) : formula L → ℕ
| formula.tt :=  sorry
| formula.ff :=  sorry
| _ := sorry
--| formula.eq  := sorry
--| formula.rel := sorry
--| formula.neg := sorry
--| formula.and := sorry
--| formula.or  := sorry
--| formula.exi := sorry
--| formula.all := sorry


-- Proof omitted for now. [Schröder–Bernstein theorem?]
constant stream.primes : stream nat.primes

-- Alternatively, we could filter out the composite numbers.
#eval list.filter nat.prime (list.range 15)

-- ⟨a, b⟩ → 2^{a+1}*3^{b+1} and so on
def encoding1 : Π n, vector ℕ n → ℕ
| 0 v     := 1
| 1 v     := (stream.primes 0)^(v.nth 0 + 1)
| (n+1) v := (stream.primes n)^(v.head + 1) * encoding1 n (v.tail)


def string_of_formula : formula L → string := sorry


#eval string.append "234" "23"

def func_number {L : lang} {n : ℕ} : L.F n → ℕ := sorry

def term_number {L : lang} : Π n, term L n → ℕ
| 0 (con c) := func_number c
| 0 (var v) := 2*v
| n (func f) := func_number f
| n (app t t₀) := term_number (n+1) t * term_number 0 t₀

-- ϕ₁ ∧ ϕ₂ := string_of_formula(∧) :: string_of_formula(ϕ₁) :: string_of_formula(ϕ₂)


/-- Completeness of Language
    ========================

All sentences are formulas.
-/

-- A set of sentences models something if every model of that theory also models
-- it.
def sentences_model {L : lang} (S : set (sentence L)) (s : sentence L) : Prop := Model S → Model s

-- Given a structure, For every formula,
-- TODO: Example: theory of groups is not complete.
def is_complete {L : lang} (S : set (formula L)) : Prop := ∀ (s : sentence L), Model S → (Model s ∨ Model ¬' s)


def is_countable (L : lang) : Prop := sorry

def sentence_to_formula {L : lang} : sentence L → formula L := sorry

-- Categoricity
--  If there is a bijection between two universes, then their models are isomorphic
def all_models_are_iso_as_structures {L : lang} (S : set (formula L)) : Prop :=
  sorry

theorem Vaught {L : lang} (S : set (formula L)) (M : Model S) :
  is_countable L → all_models_are_iso_as_structures S → is_complete S := sorry

-- TODO: Theorem: If two structures are isomorphic then they must satisfy the same theory.
-- Proof by induction on formulas.
