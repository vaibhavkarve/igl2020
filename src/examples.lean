/- In this file we demonstrate examples and constructions of various types. Key
definitions can be found in the model.lean file.

0. We define functions of arity (n : ℕ) and their API.
1. We define languages and give examples.
2. We define structures and give examples.
3. We define embedding between two structures on the same language.
4. We define terms.
   4.1 We give some examples of terms.
   4.2 We define a function for term substitution and prove a theorem.
   4.3 We give an interpretation of terms in structures.
5. We define formulas.
-/

import model


/-- We now define some example languages. We start with the simplest
possible language, the language of pure sets. This language has no
functions, relations or constants.-/
def set_lang: lang := {F := function.const ℕ empty,
                       R := function.const ℕ empty}


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
def monoid_lang : lang := {F := λ n : ℕ,
                                if n=0 then unit else        -- one constant
                                if n=2 then unit else empty, -- one binary op.
                           ..set_lang}

/-- A group is a {×, ⁻¹, 1}-structure which satisfies the identities
 1. u × (v × w) = (u × v) × w
 2. u × 1 = u
 3. 1 × u = u
 4. u × u−1 = 1
 5. u−1 × u = 1 -/
def group_lang : lang := {F := λ n : ℕ,
                               if n=0 then unit else        -- one constant
                               if n=1 then unit else        -- one unary op.
                               if n=2 then unit else empty, -- one binary op.
                          ..set_lang}

/-- A semiring is a {×, +, 0, 1}-structure which satisfies the identities
  1. u + (v + w) = (u + v) + w
  2. u + v = v + u
  3. u + 0 = u
  5. u × (v × w) = (u × v) × w
  6. u × 1 = u, 1 × u = u
  7. u × (v + w) = (u × v) + (u × w)
  8. (v + w) × u = (v × u) + (w × u)-/
def semiring_lang : lang := {F := λ n : ℕ,
                                  if n = 0 then fin 2 else          -- two constants
                                  if n = 2 then fin 2 else empty,   -- two binary ops.
                          ..magma_lang}


/-- A ring is a {×,+,−,0,1}-structure which satisfies the identities
   1. u + (v + w) = (u + v) + w
   2. u + v = v + u
   3. u + 0 = u
   4. u + (−u) = 0
   5. u × (v × w) = (u × v) × w
   6. u × 1 = u, 1 × u = u
   7. u × (v + w) = (u × v) + (u × w)
   8. (v + w) × u = (v × u) + (w × u)-/
def ring_lang : lang := {F := λ n : ℕ,
                              if n = 0 then fin 2 else        -- two constants
                              if n = 1 then fin 1 else        -- one unary op.
                              if n = 2 then fin 2 else empty, -- two binary ops.
                        ..magma_lang}

/-- An ordered ring is a ring along with a binary ordering relation {<}.-/
def ordered_ring_lang : lang := {R := λ n : ℕ,
                                if n = 2 then unit else empty,  -- one binary rel.
                                ..ring_lang}


/-- Type is a structure of the set language-/
def type_is_struc_of_set_lang {A : Type} : struc (set_lang) :=
 {univ := A,
  F := λ _ f, empty.elim f,
  R := λ _ r, empty.elim r,
  C := λ c, empty.elim c}


/-- Type is a structure of the ordered set language-/
def type_is_struc_of_ordered_set_lang {A : Type} [has_lt A]:
  struc (ordered_set_lang) :=
  {univ := A,
   F := λ _ f, empty.elim f,
   R := by {intros n r v,
            iterate {cases n, cases r},
            exact (v.nth 0 < v.nth 1),
            cases r},
   C := λ c, empty.elim c}



--
/-- We need to define a magma, because it looks like it is not defined
  in Mathlib.-/
class magma (α : Type) :=
(mul : α → α → α)


def free_magma_is_struc_of_magma_lang {A : Type} [magma A] :
  struc (magma_lang) :=
  {univ := A,
   F := by {intros n f,
            iterate {cases n, cases f}, -- if n=0,1
            exact magma.mul, -- if n=2
            cases f},        -- if n≥3
   R := λ _ r, empty.elim r,
   C := λ c, empty.elim c}


def semigroup_is_struc_of_semigroup_lang {A : Type} [semigroup A] :
  struc (semigroup_lang) :=
  {univ := A,
   F := by {intros n f,
            iterate {cases n, cases f},
            exact semigroup.mul,
            cases f},
   R := λ _ r, empty.elim r,
   C := λ c, empty.elim c}


/-- Monoid is a structure of the language of monoids-/
def monoid_is_struc_of_monoid_lang {A : Type} [monoid A] :
  struc (monoid_lang) :=
  {univ := A,
   F := by {intros n f,
            cases n, cases f,
              {exact 1},
            iterate {cases n, cases f},
            exact monoid.mul,
            cases f},
   R := λ _ r, empty.elim r,
   C := λ c, 1}


/-- Group is a structure of the group language-/
def group_is_struc_of_group_lang {A : Type} [group A] :
  struc (group_lang) :=
  {univ := A,
   F := by {intros n f,
            iterate {cases n, cases f},
              exact 1,
            iterate {cases n, cases f},
              exact group.inv,
            iterate {cases n, cases f},
              exact group.mul,
            cases f},
    R := λ _ r, empty.elim r,
    C := λ c, 1}


/-- Semiring is a structure of the language of semirings-/
def semiring_is_struc_of_semiring_lang {A : Type} [semiring A] :
  struc (semiring_lang) :=
  {univ := A,
   F := by {intros n f,
            iterate {cases n, cases f},
            cases f_val,
              exact semiring.zero,
              exact semiring.one,
            iterate {cases n, cases f},
            cases f_val,
              exact semiring.add,
              exact semiring.mul,
            cases f},
   R := λ _ r, empty.elim r,
   C := by {intros c,
            cases c,
            cases c_val,
            exact semiring.zero,
            exact semiring.one}
  }


/-- Ring is a structure of the language of rings-/
def ring_is_struc_of_ring_lang {A : Type} [ring A] :
  struc (ring_lang) :=
  {univ := A,
   F := by {intros n f,
            iterate {cases n, cases f},
            cases f_val,
              exact ring.zero,
              exact ring.one,
            iterate {cases n, cases f},
              exact ring.neg,
            iterate {cases n, cases f},
            cases f_val,
              exact ring.add,
              exact ring.mul,
            cases f},
   R := λ _ r, empty.elim r,
   C := by {intros c,
            cases c,
            cases c_val,
            exact ring.zero,
            exact ring.one}
  }


/-- Ordered ring is a structure of the language of ordered rings-/
def ordered_ring_is_struc_of_ordered_ring_lang {A : Type} [ordered_ring A]
  : struc(ordered_ring_lang) :=
  {univ := A,
   F := by {intros n f,
            iterate {cases n, cases f},
            cases f_val,
              exact ring.zero,
              exact ring.one,
            iterate {cases n, cases f},
              exact ring.neg,
            iterate {cases n, cases f},
            cases f_val,
              exact ring.add,
              exact ring.mul,
            cases f},
   R := by {intros n r v,
            iterate {cases n, cases r},
            exact (v.nth 0 < v.nth 1),
            cases r},
   C := by {intros c,
            cases c,
            cases c_val,
            exact ring.zero,
            exact ring.one}
  }


/-- A type with linear order is a structure on dense-linear-order language.-/
def LO_is_struc_of_DLO_lang {A : Type} [linear_order A] : struc (DLO_lang) :=
  {univ := A,
   R := by {intros n r v,
            iterate {cases n, cases r},
            exact (v.nth 0 < v.nth 1),
            cases r,
          },
   .. type_is_struc_of_set_lang}


/- TODO: Fix this proof.
lemma ordered_ring_is_struc_of_ordered_ring_lang {A : Type} [ordered_ring A] :
  struc (ordered_ring_lang) :=
begin
  fconstructor,
  { exact A},
  {
    intros n f,
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
end-/


/-! 4.1 Examples of Terms
    ---------------------
The following example is taken from [Marker2002]. -/

namespace example_terms
  /-- The language L has:
  - one unary function f,
  - one binary function g,
  - and one constant symbol c.-/

  def L1 : lang := {F := λ n,
                         if n=0 then unit else        -- one constant
                         if n=1 then unit else        -- one unary op.
                         if n=2 then unit else empty, -- one binrary op.
                    R := function.const ℕ empty}
  /-- f is a unary operation in L1. -/
  def f : L1.F 1 := unit.star
  /-- g is a binary operation in L1. -/
  def g : L1.F 2 := unit.star
  /-- c is a constant in L1. -/
  def c : L1.C := unit.star

  /-- M1 is a structure on L1. -/
  def M1 : struc L1 :=
  {univ := ℕ,
   F := by {intros n f,
            cases n, { exact 1},               -- if n=0 (must match with M1.C)
            cases n, { exact λ x : ℕ, 100*x}, -- if n=1
            cases n, { exact (+)},             -- if n=2
            cases f},                          -- if n>2
   R := λ _ f _, by {cases f},
   C := function.const L1.C 1}


  open term

  /-- t = f(g(c, f(v₅))) is a term on language L1.-/
  def t₁ : term L1 0 := app (func f) (var 5)            -- f(c)
  def t₂ : term L1 0 := app (app (func g) (con c)) t₁   -- g(c)(t₁)
  def t₃ : term L1 0 := app (func f) t₂                 -- f(t₂)
  def t : term L1 0 := app (func f)
                           $ app (app (func g) (con c))
                                 $ app (func f) (con c)
  def va : ℕ → M1.univ := function.const ℕ (M1.C c)

  #reduce term_interpretation M1 va (func f)  -- f is interpreted as x ↦ 100x
  #reduce term_interpretation M1 va (func g)  -- g is interpreted (x, y) ↦ x+y
  #reduce term_interpretation M1 va (con c)   -- c is interpreted as (1 : ℕ)
  #reduce term_interpretation M1 va t₁          -- f(c) is interpreted as 100
  #reduce term_interpretation M1 va t₂          -- g(c, t₁) is interpreted as 101
  #reduce term_interpretation M1 va t₃          -- f(g(c, f(c))) is interpreted as 10100
  #reduce term_interpretation M1 va t           -- same as t₃


  def t₄ : term L1 0 := app (func f) (var 5) -- f(v₅)
  def t₅ : term L1 0 := app (app (func g) (con c)) (var 4) -- g(c, v₄)
  #reduce term_sub t₅ 0 t₄ -- f(g(c, v₄))
  #reduce term_sub (var 3) 0 t₄ -- f(v₃)
  #reduce term_sub_for_var (var 3) 4 0 t₄ -- f(v₅)
  #reduce term_sub_for_var (var 3) 5 0 t₄ -- f(v₃)

  open example_terms
  def ψ₁ : formula L1 := t₁ =' (var 5) -- f(c) = v₅
  def ψ₂ : formula L1 := ¬' (var 4 =' t₃ ) -- g(c, t₁) =/= v₄
  def ψ₃ : formula L1 := ∃' 3 ψ₁ -- ∃v₃  f(v₅) = v₅
  def ψ₄ : formula L1 := ∀' 4 (∀' 5 ψ₂) -- ∀v₄∀v₅ g(c, f(v₄)) =/= v₅

  example : var_is_bound 5 (ψ₄) :=
  begin
    unfold var_is_bound,
    rw ψ₄,
    unfold is_var_free,
    rw ψ₂,
    simp,
  end

  #reduce is_sentence (ψ₂)
  #reduce is_sentence (ψ₃)
  #reduce is_sentence (ψ₄)

end example_terms



namespace DLO_Model

@[reducible] def Q_struc : struc DLO_lang :=
 { univ := ℚ,
   R := λ n f, by {iterate 2 {cases n, exact ∅},
                   cases n, exact {v : vector ℚ 2 | v.nth 0 < v.nth 1},
                   exact ∅},
  C := function.const DLO_lang.C 1,
  F := λ _ f, by {cases f},
 }
notation `<'` : 110 := formula.rel 2 ()

/- A dense linear ordering without endpoints is a language containg a
    single binary relation symbol < satisfying the following sentences:
-- 1. ∀x x < x;
-- 2. ∀x ∀y ∀z (x < y → (y < z → x < z));
-- 3. ∀x ∀y (x < y ∨ x = y ∨ y < x);
-- 4. ∀x ∃y x < y;
-- 5. ∀x ∃y y < x;
-- 6. ∀x ∀y (x < y → ∃z (x < z ∧ z < y)). -/

open term
def mk_vec (v₁ v₂ : ℕ) : vector (term DLO_lang 0) 2 := ⟨[var v₁, var v₂], rfl⟩
def φ₁ : formula DLO_lang := <' $ mk_vec 1 2 -- x < y
def φ₂ : formula DLO_lang := <' $ mk_vec 2 1 -- y < x
def φ₃ : formula DLO_lang := <' $ mk_vec 2 3 -- y < z
def φ₄ : formula DLO_lang := <' $ mk_vec 3 2 -- z < y
def φ₅ : formula DLO_lang := <' $ mk_vec 1 3 -- x < z
def φ₆ : formula DLO_lang := <' $ mk_vec 1 1 -- x < x

def DLO_axioms : set(formula DLO_lang) :=
 { ∀'1 (∀'2 (¬' φ₆)),
   ∀'1 (∀'2 (∀'3 (φ₁ →' (φ₃ →' φ₅)))),
   ∀'1 (∀'2 (∀' 3 ((φ₁ ∨' φ₂) ∨' (var 1 =' var 2)))),
   ∀'1 (∃'2 (φ₁)),
   ∀'1 (∃'2 (φ₂)),
   ∀'1 (∀'2 (φ₁ →' ∃'3(φ₅ ∧' φ₄)))}

def Q_Model_DLO : Model (DLO_axioms) :=
 { M := Q_struc,
   va := function.const ℕ 0,
   satis := begin
intros σ,
rintro (rfl | rfl | rfl | rfl | rfl | H);
iterate {unfold models},
--intros,
 {intros x x₁ h,
  cases h,
  solve_by_elim},
 { rintros x x₁ x₂ h,
   simp at *,
   unfold models at h,
   cases h,
   unfold φ₁ at h,
   unfold models at h,
   simp at h,
   cases h,
   simp at *,
   dsimp at *,
 sorry,
 sorry},
 sorry,
 intros,
  {
    use x+1,
    fconstructor,
    suffices h : x ≤ x+1,
    exact h,
    norm_num,
    suffices h : ¬(x+1≤x),
    exact h,
    linarith,
  },
 intros,
  {
    use x-1,
    fconstructor,
    suffices h : x-1 ≤ x,
    exact h,
    linarith,
    suffices h : ¬(x≤x-1),
    exact h,
    linarith,
  },
 sorry,
 end
}


end DLO_Model