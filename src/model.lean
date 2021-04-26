import tactic
import data.real.basic
import set_theory.cardinal

-- Local imports
import func lang struc


/-!
# model.lean

In this file, we define
- Terms
  - we define a function for term substitution and prove a theorem.
  - we give an interpretation of terms in structures.
- Formulas
- Models and Theories
-

## Tags

model theory, o-minimality
-/


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

namespace term
variables {L : lang} {M : struc L}


/-- This function computes the depth of a term as seen by a parser. For
    example, the depth of `f(v₁, v₂, v₃)` is 4 (one for `f` and one for
    each variable). The depth of `f(v₁, g(v₂), v₃)` is similarly 5.
-/
def depth : Π {n : ℕ}, term L n → ℕ
| 0 (con c)    := 1
| 0 (var v)    := 1
| _ (func f)   := 1
| _ (app t t₀) := t.depth + t₀.depth


/-- Every language L is guaranteed to have a 0-level term because
variable terms can be formed without reference to L. In fact, every
language has countably infinite terms of level 0.
-/
instance inhabited : inhabited (term L 0) :=
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
| _ (func f)   := M.F f
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

end term

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

namespace formula
variables {L : lang} {M : struc L}

infix    ` =' ` :  80 := eq
prefix   ` ¬' ` :  60 := neg
infix    ` ∧' ` :  70 := and
infix    ` ∨' ` :  70 := or
notation ` ∃' ` : 110 := exi
notation ` ∀' ` : 110 := all
notation ` ⊤' ` : 110 := tt
notation ` ⊥' ` : 110 := ff

def impl (φ₁ : formula L) (φ₂ : formula L) := ¬'φ₁ ∨' φ₂
infix ` →' ` : 80 := impl

def bicond (φ₁ : formula L) (φ₂ : formula L) := (φ₁ →' φ₂)∧'(φ₂ →' φ₁)
infix ` ↔' ` : 80 := bicond


/-- Helper function for variables from list of terms-/
@[reducible] def vars_in_list : list (term L 0) → finset ℕ
| [] := ∅
| (t :: ts) := t.vars_in_term ∪ vars_in_list ts


/-- Extracts set of variables from the formula-/
@[reducible] def vars_in_formula : formula L → finset ℕ
| ⊤'                 := ∅
| ⊥'                 := ∅
| (t₁='t₂)           := t₁.vars_in_term ∪ t₂.vars_in_term
| (formula.rel _ ts) := vars_in_list (ts.to_list)
| (¬' ϕ)             := vars_in_formula ϕ
| (ϕ₁ ∧' ϕ₂)         := vars_in_formula ϕ₁ ∪ vars_in_formula ϕ₂
| (ϕ₁ ∨' ϕ₂)         := vars_in_formula ϕ₁ ∪ vars_in_formula ϕ₂
| (∃' v ϕ)           := vars_in_formula ϕ ∪ {v}
| (∀' v ϕ)           := vars_in_formula ϕ ∪ {v}

/- The set of L-formulas for any language L must have ⊤ as a formula -/
instance inhabited {L : lang} : inhabited (formula L) :=
  {default := formula.tt}

/-- A variable occurs freely in a formula
    1. if it occurs in the formula, AND
    2. if at least one of its occurrences is outside of a quantification.

    For example, this function returns `false` on input `(var, ϕ)` in any of
    the following scenarios --
    - `var` does not occur in `ϕ` at all.
    - `var` occurs in `ϕ` but only after a quantifier.-/
@[reducible] def var_occurs_freely (var : ℕ) : formula L → Prop
| ⊤'                 := false  -- doesn't occur
| ⊥'                 := false  -- doesn't occur
| (t₁='t₂)           := var ∈ t₁.vars_in_term ∪ t₂.vars_in_term -- check occur
| (formula.rel _ ts) := var ∈ vars_in_list (ts.to_list)         -- check occur
| (¬' ϕ)             := var_occurs_freely ϕ
| (ϕ₁ ∧' ϕ₂)         := var_occurs_freely ϕ₁ ∨ var_occurs_freely ϕ₂
| (ϕ₁ ∨' ϕ₂)         := var_occurs_freely ϕ₁ ∨ var_occurs_freely ϕ₂
| (∃' v ϕ)           := (var ≠ v) ∧ var_occurs_freely ϕ -- check not quantified
| (∀' v ϕ)           := (var ≠ v) ∧ var_occurs_freely ϕ -- check not quantified

end formula

/-- A formula in which no variable occurs freely is a sentence.  We create a
    subtype of `L`-formulas that we call `L`-sentences.-/
def sentence (L : lang) : Type :=
  {ϕ : formula L // ∀ var, ¬ var_occurs_freely var ϕ}

variables (ϕ : formula L) (σ: sentence L)

/-- Since sentences are a subtype of formula, we define a coercion map for
    conveniently casting any sentence `σ` to a formula by writing `↑σ`.-/
instance coe_sentence_formula : has_coe (sentence L) (formula L) := ⟨λ σ, σ.val⟩

/- The formula ⊤ previously used to prove that formulas are inhabited is also
   vacuously a sentence -/
instance sentence.inhabited {L : lang} : inhabited (sentence L) :=
  {default := ⟨⊤', by tauto⟩}

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

def models_sentence (M : struc L) (σ : sentence L) : Prop :=
  ∃ va : ℕ → M.univ, va ⊨ σ
notation M` ⊨ `σ : 100 := models_sentence M σ -- Type this as a variant of \entails.

lemma models_formula_or_negation (va : ℕ → M.univ) :
  models_formula va ϕ ∨ models_formula va (¬' ϕ) :=
begin
  by_cases (va ⊨ ϕ),
  repeat {tauto},
end

lemma neg_of_sentence_is_sentence :
   ∀ var, ¬ var_occurs_freely var (¬' (↑σ : formula L)) :=
begin
  intros var,
  exact σ.property var,
end

def neg_sentence : sentence L := ⟨¬' ↑σ, neg_of_sentence_is_sentence σ⟩
prefix ` ¬' ` :  60 := neg_sentence


lemma models_sentence_or_negation (M : struc L) (σ : sentence L) :
  models_sentence M σ ∨ models_sentence M (¬' σ) :=
begin
  by_cases (M ⊨ σ),
    {tauto},
  right,
  unfold models_sentence at *,
  push_neg at h,
  simp only [coe, subtype.val_eq_coe],
  haveI M.univ_inhabited := M.univ_inhabited,
  use function.const ℕ (default M.univ),
  apply h,
end


/-- We say that two `L`-structures `M` and `N` are elementarily equivalent
and write `M ≡ N` if : `M ⊨ φ` if and only if `N ⊨ φ` for all `L`-sentences
`φ`.-/
def elementarily_equivalent (M₁ M₂: struc L) : Prop :=
  ∀ (σ : sentence L), (M₁ ⊨ σ) ↔ M₂ ⊨ σ
infix ` ≡ ` := elementarily_equivalent


/-- The full theory of `M` is the set of `L`-sentences `φ` such that `M ⊨ φ`.-/
def full_theory (M : struc L) : set (sentence L) := {ϕ : sentence L | M ⊨ ϕ}


/-- `M ≡ N` iff their full theories match.-/
lemma eq_full_theory_iff_elementary_equivalent {M N : struc L} :
      full_theory M = full_theory N ↔ M ≡ N :=
begin
  simp only [elementarily_equivalent, set_of, full_theory] at *,
  split,
  { intros h σ,
    rwa h},
  { intro h,
    ext σ,
    finish}
end


-- TODO: Theorem: If two structures are isomorphic then they must satisfy the
-- same theory.  Proof by induction on formulas.
theorem isomorphic_struc_satisfy_same_theory {M₁ M₂ : struc L}
  (η : isomorphism M₁ M₂) {σ : sentence L} : M₁ ⊨ σ → M₂ ⊨ σ :=
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


-- TODO: But put this on hold till we figure out how to prove that the
-- inverse of bijective function is bijective.
noncomputable def isomorphism_inverse (M N : struc L) [nonempty M.univ] [nonempty N.univ]
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
    repeat{sorry}},
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
   {exact isomorphic_struc_satisfy_same_theory η},
   { sorry},
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
  (σ : sentence L) :
  xor (∀ va : ℕ → M.univ, va ⊨ σ.val) (∀ va' : ℕ → M.univ, ¬ va' ⊨ σ.val) :=
begin
  unfold xor,
  cases σ with ϕ hϕ,
  simp,
  haveI Muniv_in := M.univ_inhabited,
  have va := function.const ℕ (default M.univ),
  cases ϕ,
    case formula.tt
    { simp [models_formula]},         -- every var-assignment satisfies ⊤'
    case formula.ff
    { simp [models_formula]},         -- every var-assign falsifies ⊥'
    case formula.eq : t₁ t₂
    { simp [models_formula],          -- Question/TODO: Not sure how to proceed.
      sorry },
    case formula.rel : n r vec
    { admit },
    case formula.neg : ϕ₁
    { admit },
    case formula.and : ϕ₁ ϕ₂
    { admit },
    case formula.or : ϕ₁ ϕ₂
    { admit },
    case formula.exi : x ϕ₁
    { admit },
    case formula.all : x ϕ₁
    { admit },
end


/-- An `L`-theory `T` is simply a set of `L`-sentences. We say that `M` is
a model of `T` and write `M ⊨ T` if `M ⊨ φ` for all sentences `φ ∈ T`.-/
def theory (L : lang) : Type := set (sentence L)

namespace theory
  /-- Add standard instances for theories. Each instance is derived from the
  parent type `set (sentence L).-/
  instance has_mem : has_mem (sentence L) (theory L) := set.has_mem
  instance has_singleton : has_singleton (sentence L) (theory L) :=
    set.has_singleton
  instance has_union : has_union (theory L) := set.has_union
  instance has_subset : has_subset (theory L) := set.has_subset
  /- There always exists an L-theory, having a single sentence given by {⊤'},
     since ⊤' is always guaranteed to be a sentence -/
  instance inhabited {L : lang} : inhabited (theory L) := set.inhabited
end theory
variable T : theory L

/-- We now define a model to be a structure that models a set of sentences
and show `(ℚ, <)` models the axioms for DLO.-/
structure Model :=
(M : struc L)
(satis {σ : sentence L} : σ ∈ T → M ⊨ σ)

def Model.card {T : theory L} (μ : Model T) : cardinal := μ.M.card


/-- We say that a theory is satisfiable if it has a model.-/
def satisfiable_theory : Prop := nonempty (Model T)



/-! ## Completeness of Language-/

/-- A set of sentences models something if every model of that theory also
 models it.-/
def logical_consequence : Prop := ∀ μ : Model T, μ.M ⊨ σ

structure proof (T : theory L) (ϕ : formula L) : Type :=
(steps : list (formula L))
(steps_nonempty : steps ≠ [] := by tauto)
(conclusion : list.last steps steps_nonempty = ϕ)

def proves : Prop := nonempty (proof T ϕ)


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
  have H₁ : A₁.M ⊨ σ := A₁.satis h,
  have H₂ : A₂.M ⊨ σ := A₂.satis h,
  tauto,

  have va : ℕ → A₁.M.univ := sorry,
  --have H₁ : models_formula va A₁.M (¬' ↑σ) := suggest,
  sorry,
end


class has_infinite_model (T : theory L) : Type 1 :=
(μ : Model T)
(big : cardinal.omega ≤ μ.card)


lemma has_infinite_model_union_theory (t : theory L) (σ : sentence L)
 [has_infinite_model t] : has_infinite_model (t ∪ {σ}) :=
begin
 sorry
end

/-- Lowenheim-Skolem asserts that for a theory over a language L, if that theory
    has an infinite model, then it has a model for any infinite cardinality
    greater than or equal to |L|-/
axiom LS_Lou [has_infinite_model T] {k : cardinal}
  (kbig : cardinal.omega ≤ k) (h : L.card ≤ k) :
  ∃ μ : Model T, μ.card = k


/- A theory is k-categorical if all models of cardinality k are isomorphic as
   structures.-/
def theory_kcategorical (k : cardinal) (T : theory L) :=
  ∀ (M₁ M₂ : Model T), M₁.card = k ∧ M₂.card = k
  → nonempty (isomorphism M₁.M M₂.M)


/-- A theory can always be extended by sentences modeled by its struc. Here, we
define the singleton-version of this result.
-/
def model_of_extended {T : theory L} {μ : Model T} {σ : sentence L}
  (sat_σ: μ.M ⊨ σ) : Model (T ∪ {σ}) :=
  ⟨μ.M, λ σ' H, by {cases H, exact μ.satis H, rwa [← H.symm]}⟩

def model_of_subset {t s : theory L} (M : Model t) (H : s ⊆ t) : Model s :=
  {M := M.M,
   satis := λ σ h,  M.satis (set.mem_of_subset_of_mem H h)}


instance infinite_model_of_theory_extended {T : theory L} {μ₁ : Model T} {σ : sentence L}
  (models_infinite : ∀ (μ : Model T), cardinal.omega ≤ μ.card)
  (h₁ : μ₁.M ⊨  σ) :
  has_infinite_model (T ∪ {σ}) :=
⟨model_of_extended h₁, models_infinite μ₁⟩



/-- If a theory is k-categorical and has an infinite model,
    it is complete.-/
theorem Vaught (k : cardinal) (h : L.card ≤ k) (kbig : cardinal.omega ≤ k)
  (models_infinite : ∀ (μ : Model T), cardinal.omega ≤ μ.card)
  (hkc : theory_kcategorical k T)
  : is_complete_theory T :=
begin
  intros A₁ A₂ σ,
  split,
  { intro A₁_sat_σ,
    -- We extend the theory T with sentence σ. T has an infinite model. We
    -- prove that T∪{σ} also has an infinite model.
    haveI has_infinite_model_T_σ
      := infinite_model_of_theory_extended models_infinite A₁_sat_σ,

    -- We proceed to write a proof by contradiction.
    by_contradiction A₂_unsat_σ,
    have A₂_sat_neg_σ : A₂.M ⊨ ¬' σ,
      { have A₂_sat_or_unsat_σ, from models_sentence_or_negation A₂.M σ,
        tauto},

    -- Show that an infinite model exists if we extend the theory T with
    -- sentence ¬'σ.
    haveI has_infinite_model_T_neg_σ
      := infinite_model_of_theory_extended models_infinite A₂_sat_neg_σ,

    -- Invoke the Lowenheim-Skolem axiom to obtain models A₃ and A₄ of T
    -- with σ and ¬'σ respectively. More importantly, both models have the
    -- same cardinality.
    obtain ⟨A₃, A₃card⟩ := LS_Lou (T ∪ {σ}) kbig h,
    obtain ⟨A₄, A₄card⟩ := LS_Lou (T ∪ {¬'σ}) kbig h,
    -- Construct models of T from A₃ and A₄ (restricting the theory to a
    -- subset).
    let A₅ : Model T := model_of_subset A₃ (by norm_num),
    let A₆ : Model T := model_of_subset A₄ (by norm_num),

    -- Since A₄ does not satisfy σ, every variable assignment must evaluate
    -- σ to false.
    rcases models_formula_all_or_none_sentences A₄.M σ with ⟨h₁,__⟩ | ⟨h₂,__⟩,
      { -- If all variable assignments satisfiy σ, then we get
        -- contradiction via A₄_satis.
        obtain ⟨va, hva⟩ : A₄.M ⊨ ¬'σ, from A₄.satis (by norm_num),
        tauto},

      { -- If all variable assignments falsify σ, then we get contradiction
        -- via the fact the A₅ and A₆ are isomorphic, but they satisfy σ
        -- and ¬'σ respectively.
        have iso : isomorphism A₅.M A₆.M,
          from nonempty.some (hkc A₅ A₆ ⟨A₃card, A₄card⟩),
        have h₃ : A₃.M ⊨ σ, from A₃.satis (by norm_num),
        obtain ⟨va', hva'⟩ : A₆.M ⊨ σ,
          from isomorphic_struc_satisfy_same_theory iso h₃,
        tauto},
    },
  sorry, -- Symmetric. The same proof as above should work. TODO: turn it
         -- into two lemmas.
end

#exit

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
