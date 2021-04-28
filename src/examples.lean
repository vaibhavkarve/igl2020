/- In this file we demonstrate examples and constructions of various types. Key
definitions can be found in the model.lean file.-/

import model


/-- We now define some example languages. We start with the simplest
possible language, the language of pure sets. This language has no
functions, relations or constants.-/
def set_lang: lang := {F := function.const ℕ+ empty,
                       R := function.const ℕ+ empty,
                       C := empty}


/-- The language of ordered sets is the language or sets with a binary
  ordering relation {<}.-/
def ordered_set_lang: lang := {R := λ n : ℕ+, if n=2 then unit else empty,
                               ..set_lang}

/-- A magma is a {×}-structure. So this has 1 function, 0 relations and
0 constants.-/
def magma_lang : lang := {F := λ n : ℕ+, if n=2 then unit else empty,
                          ..set_lang}


/-- A semigroup is a {×}-structure which satisfies the identity
  u × (v × w) = (u × v) × w.  Note that identities are not relations!-/
def semigroup_lang : lang := magma_lang

/-- A monoid is a {×, 1}-structure which satisfies the identities
   1. u × (v × w) = (u × v) × w
   2. u × 1 = u
   3. 1 × u = u. -/
def monoid_lang : lang := {F := λ n : ℕ+,
                                if n=2 then unit else empty, -- one binary op.,
                           C := unit,                        -- one constant
                           R := function.const ℕ+ empty}

/-- A group is a {×, ⁻¹, 1}-structure which satisfies the identities
 1. u × (v × w) = (u × v) × w
 2. u × 1 = u
 3. 1 × u = u
 4. u × u−1 = 1
 5. u−1 × u = 1 -/
def group_lang : lang := {F := λ n : ℕ+,
                               if n=1 then unit else        -- one unary op.
                               if n=2 then unit else empty, -- one binary op.
                          C := unit,                        -- one constant
                          ..set_lang}

/-- A semiring is a {×, +, 0, 1}-structure which satisfies the identities
  1. u + (v + w) = (u + v) + w
  2. u + v = v + u
  3. u + 0 = u
  5. u × (v × w) = (u × v) × w
  6. u × 1 = u, 1 × u = u
  7. u × (v + w) = (u × v) + (u × w)
  8. (v + w) × u = (v × u) + (w × u)-/
def semiring_lang : lang := {F := λ n : ℕ+,
                                  if n = 2 then fin 2 else empty, -- two binary ops.
                             C := fin 2,                     -- two constants
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
def ring_lang : lang := {F := λ n : ℕ+,
                              if n = 1 then fin 1 else        -- one unary op.
                              if n = 2 then fin 2 else empty, -- two binary ops.
                         C := fin 2,                          -- two constants
                         ..magma_lang}

/-- An ordered ring is a ring along with a binary ordering relation {<}.-/
def ordered_ring_lang : lang := {R := λ n : ℕ+,
                                if n = 2 then unit else empty,  -- one binary rel.
                                ..ring_lang}


/-- An inhabited type is a structure of the set language-/
def type_is_struc_of_set_lang {A : Type} [inhabited A] : struc (set_lang) :=
 {univ := A,
  F := λ _, empty.elim,
  R := λ _, empty.elim,
  C := empty.elim}


/-- Type is a structure of the ordered set language-/
def type_is_struc_of_ordered_set_lang {A : Type} [has_lt A] [inhabited A]:
  struc (ordered_set_lang) :=
  {univ := A,
   F := λ _, empty.elim,
   R := λ n r v, by {repeat {cases n <|> unfold_coes at v <|> linarith
                             <|> cases r <|> cases n_val},
                     exact (v.nth 0 < v.nth 1)},
   C := empty.elim}



/-- We need to define a magma, because it looks like it is not defined
  in Mathlib.-/
class magma (α : Type) :=
(mul : α → α → α)


def free_magma_is_struc_of_magma_lang {A : Type} [magma A] [inhabited A] :
  struc (magma_lang) :=
  {univ := A,
   F := λ n f, by {repeat {cases n with n_val _ <|> unfold_coes <|> cases f
                    <|> linarith <|> cases n_val},
                   exact magma.mul}, -- if n=2
   R := λ _, empty.elim,
   C := empty.elim}


def semigroup_is_struc_of_semigroup_lang {A : Type} [semigroup A] [inhabited A] :
  struc (semigroup_lang) :=
  {univ := A,
   F := λ n f, by {repeat {cases n <|> linarith <|> cases f <|> cases n_val},
                   exact semigroup.mul},
   R := λ _, empty.elim,
   C := empty.elim}


/-- Monoid is a structure of the language of monoids-/
def monoid_is_struc_of_monoid_lang {A : Type} [monoid A] :
  struc (monoid_lang) :=
  {univ := A,
   F := λ n f, by {repeat {cases n <|> cases f <|> linarith <|> cases n_val},
                   exact monoid.mul},
   R := λ _, empty.elim,
   C := 1,
   univ_inhabited := ⟨1⟩}

/-- Group is a structure of the group language-/
def group_is_struc_of_group_lang {A : Type} [group A] :
  struc (group_lang) :=
  {univ := A,
   F := λ n f, by {repeat {cases n <|> linarith <|> cases f <|> cases n_val},
                   exact group.inv,
                   exact group.mul},
   ..monoid_is_struc_of_monoid_lang}


/-- Semiring is a structure of the language of semirings-/
def semiring_is_struc_of_semiring_lang {A : Type} [semiring A] :
  struc (semiring_lang) :=
  {univ := A,
   F := λ n f, by {cases n, cases n_val,
                     {linarith},
                   cases n_val, cases f,
                   cases n_val, cases f,
                     {cases f_val,
                      exact (+),
                      exact (*)},
                   cases f},
   R := λ _, empty.elim,
   C := λ c, by {cases c, cases c_val, exact 0, exact 1},
   univ_inhabited := ⟨0⟩}


/-- Ring is a structure of the language of rings-/
def ring_is_struc_of_ring_lang {A : Type} [ring A] :
  struc (ring_lang) :=
  {univ := A,
   F := λ n f, by {cases n, cases n_val,
                     {linarith},
                   cases n_val,
                     {exact ring.neg},
                   cases n_val, cases f,
                     {cases f_val,
                      exact (+),
                      exact (*)},
                   cases f},
   ..semiring_is_struc_of_semiring_lang}


/-- Ordered ring is a structure of the language of ordered rings-/
def ordered_ring_is_struc_of_ordered_ring_lang {A : Type} [ordered_ring A]
  : struc(ordered_ring_lang) :=
  {univ := A,
   R := λ n r v, by {cases n, cases n_val,
                       {linarith},
                     cases n_val, cases r,
                       {unfold_coes at v,
                        exact v.nth 0 < v.nth 1}},
   ..ring_is_struc_of_ring_lang}


/-- A type with linear order is a structure on dense-linear-order language.-/
def LO_is_struc_of_DLO_lang {A : Type} [linear_order A] [inhabited A]
 : struc (lang.DLO_lang) :=
  {univ := A,
   R := λ n r v, by {cases n, cases n_val,
                       {linarith},
                     cases n_val, cases r,
                       {unfold_coes at v,
                        exact (v.nth 0 < v.nth 1)}},
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

  def L1 : lang := {F := λ (n : ℕ+),
                         if n=1 then unit else        -- one unary op.
                         if n=2 then unit else empty, -- one binrary op.
                    R := function.const ℕ+ empty,
                    C := unit}
  /-- f is a unary operation in L1. -/
  def f : L1.F 1 := unit.star
  /-- g is a binary operation in L1. -/
  def g : L1.F 2 := unit.star
  /-- c is a constant in L1. -/
  def c : L1.C := unit.star

  /-- M1 is a structure on L1. -/
  def M1 : struc L1 :=
  {univ := ℕ,
   F := λ n f, by {cases n, cases n_val,
                     { linarith},
                   cases n_val,
                     { exact λ x : ℕ, 100*x}, -- if n=1
                   cases n_val,
                     { exact (+)},             -- if n=2
                   cases f},                   -- if n>2
   R := λ _, empty.elim,
   C := λ c, 1,
   }


  open term

  /-- t = f(g(c, f(v₅))) is a term on language L1.-/
  def t₁ : term L1 0 := app (func f) (var 5)            -- f(c)
  def t₂ : term L1 0 := app (app (func g) (con c)) t₁   -- g(c)(t₁)
  def t₃ : term L1 0 := app (func f) t₂                 -- f(t₂)
  def t : term L1 0 := app (func f)
                           $ app (app (func g) (con c))
                                 $ app (func f) (con c)
  def va : ℕ → M1.univ := function.const ℕ (M1.C c)

  #reduce term_interpretation va (func f)  -- f is interpreted as x ↦ 100x
  #reduce term_interpretation va (func g)  -- g is interpreted (x, y) ↦ x+y
  #reduce term_interpretation va (con c)   -- c is interpreted as (1 : ℕ)
  #reduce term_interpretation va t₁          -- f(c) is interpreted as 100
  #reduce term_interpretation va t₂          -- g(c, t₁) is interpreted as 101
  #reduce term_interpretation va t₃          -- f(g(c, f(c))) is interpreted as 10100
  #reduce term_interpretation va t           -- same as t₃


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

  example : ¬ (formula.var_occurs_freely 5 ψ₄) :=
  begin
    rw ψ₄,
    unfold formula.var_occurs_freely,
    rw ψ₂,
    simp,
  end

  def phi : formula (lang.DLO_lang) :=
  ¬'(∀' 2 ⊤') ∧' ((var 1) =' (var 4)) ∧' (∃' 3 (var 2 =' var 3))

  example :   formula.var_occurs_freely 1 phi :=
    by norm_num [phi, formula.var_occurs_freely]
  example :   formula.var_occurs_freely 2 phi :=
    by norm_num [phi, formula.var_occurs_freely]
  example : ¬ formula.var_occurs_freely 3 phi :=
    by norm_num [phi, formula.var_occurs_freely]
  example :   formula.var_occurs_freely 4 phi :=
    by norm_num [phi, formula.var_occurs_freely]
  example : ¬ formula.var_occurs_freely 5 phi :=
    by norm_num [phi, formula.var_occurs_freely]


end example_terms



namespace DLO_Model

@[reducible] def Q_struc : struc lang.DLO_lang :=
 { univ := ℚ,
   R := λ n f, by { cases n, cases n_val,
                      {linarith},
                    cases n_val,
                      {exact ∅},
                    cases n_val,
                      {exact {v : vector ℚ 2 | v.nth 0 < v.nth 1}},
                    exact ∅},
  F := λ _, empty.elim,
  C := empty.elim
 }
notation `<'` : 110 := @formula.rel lang.DLO_lang 2 ()

/- A dense linear ordering without endpoints is a language containg a
    single binary relation symbol < satisfying the following sentences:
-- 1. ∀x x < x;
-- 2. ∀x ∀y ∀z (x < y → (y < z → x < z));
-- 3. ∀x ∀y (x < y ∨ x = y ∨ y < x);
-- 4. ∀x ∃y x < y;
-- 5. ∀x ∃y y < x;
-- 6. ∀x ∀y (x < y → ∃z (x < z ∧ z < y)). -/

open term
@[reducible] def mk_vec (v₁ v₂ : ℕ) : vector (term lang.DLO_lang 0) 2 := ⟨[var v₁, var v₂], rfl⟩
@[reducible] def φ₁ : formula lang.DLO_lang := <' $ mk_vec 1 2 -- x < y
@[reducible] def φ₂ : formula lang.DLO_lang := <' $ mk_vec 2 1 -- y < x
@[reducible] def φ₃ : formula lang.DLO_lang := <' $ mk_vec 2 3 -- y < z
@[reducible] def φ₄ : formula lang.DLO_lang := <' $ mk_vec 3 2 -- z < y
@[reducible] def φ₅ : formula lang.DLO_lang := <' $ mk_vec 1 3 -- x < z
@[reducible] def φ₆ : formula lang.DLO_lang := <' $ mk_vec 1 1 -- x < x

def DLO_axioms : set (formula lang.DLO_lang) :=
 { ∀'1 (¬' φ₆),
   ∀'1 (∀'2 (∀'3 (φ₁ →' (φ₃ →' φ₅)))),
   ∀'1 (∀'2 ((φ₁ ∨' φ₂) ∨' (var 1 =' var 2))),
   ∀'1 (∃'2 (φ₁)),
   ∀'1 (∃'2 (φ₂)),
   ∀'1 (∀'2 (φ₁ →' ∃'3(φ₅ ∧' φ₄)))}


def DLO_theory : set (sentence lang.DLO_lang) :=
 { ⟨∀'1 (¬' φ₆), by {finish [formula.var_occurs_freely]}⟩,
   ⟨∀'1 (∀'2 (∀'3 (φ₁ →' (φ₃ →' φ₅)))),
     by {push_neg,
         rintros _ _ _ _ (⟨_ | _ | _⟩ | ⟨_ | _ | _⟩ | _ | _ | _);
         tauto}⟩,
   ⟨∀'1 (∀'2 (∀' 3 ((φ₁ ∨' φ₂) ∨' (var 1 =' var 2)))),
     by {push_neg,
         rintro (_ | _ | _ | _ | _ | _) _ _ _;
         exact dec_trivial <|> tauto}⟩,
   ⟨∀'1 (∃'2 (φ₁)),
     by {push_neg,
         rintros _ _ _ (_ | _ | _);
         tauto}⟩,
   ⟨∀'1 (∃'2 (φ₂)),
        by {push_neg,
            rintros _ _ _ (_ | _ | _);
            tauto}⟩,
   ⟨∀'1 (∀'2 (φ₁ →' ∃'3(φ₅ ∧' φ₄))),
        by {push_neg,
            rintros _ _ _ (⟨_ | _ | _⟩ | ⟨_, ⟨_ | _ | _⟩ | _ | _ | _⟩);
            tauto}⟩,
  }


def Q_Model_DLO : Model (DLO_theory) :=
 { M := Q_struc,
   satis :=
   begin
     rintros σ (⟨_, _⟩ | x | _ | ⟨_, _⟩ | ⟨_, _⟩ | H);
     use function.const ℕ (42 : ℚ), -- 42 is just an arbitrary value
     { rintros _ _ ⟨_, _⟩, tauto},
     { sorry },
     { sorry },
     { intros x,
       use x+1,
       split;
         simp only [vector.map, list.map, vector.nth, vector.head,
                    fin.val_one, term_interpretation, rat.le,
                    function.update_same, list.nth_le];
         norm_num;
         try {ring};
         dec_trivial},
     { intros x,
       use x-1,
       split;
         simp only [vector.map, list.map, vector.nth, vector.head,
                    fin.val_one, term_interpretation, rat.le,
                    function.update_same, list.nth_le];
         norm_num;
         try {ring};
         dec_trivial},
     repeat {sorry},
end



#exit



/-- DLO is complete by using Vaught's test. This will include the
    back-and-forth argument (Lou) which includes construct a sequence of
    partial isomorphisms and then stitch it together to create a big
    isomoprhism by zig-zagging back and forth over countable models of
    DLO.-/
theorem DLO_is_complete : complete_theory DLO_theory := sorry


end DLO_Model
