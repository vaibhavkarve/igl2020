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
   4.2 We define a function for term substitution and prove a theorem.
   4.3 We give an interpretation of terms in structures.
5. We define formulas.
-/


/-! -----------------------------------------------------------------
-- 0. Arity n Functions and their API
-- ----------------------------------------------------------------/

/-- Inductively define a function on n arguments. 0-arity functions are just
terms of type α.-/
@[reducible] def Func (α : Type) : ℕ → Type
| 0 := α
| (n+1) := α → Func n

/-- Create a type of ALL functions with finite arity. Here we use Σ to
sum up the types. Sum for types :: union for sets.-/
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
| (n+1) := λ f a, mk_Func_of_total (λ v, f (a :: v))  -- an (n+2)-ary function


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


/-- Apply a Func to a function on `fin n`.-/
def app_fin {α : Type} {n : ℕ} (f : Func α (n+1)) (v : fin (n+1) → α) : α :=
  app_vec f (vector.of_fn v)


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


/-! -----------------------------------------------------------------
-- 1. Languages and Examples
-- ----------------------------------------------------------------/

/-- A language is given by specifying functions, relations and constants
along with the arity of each function and each relation.-/
structure lang : Type 1 :=
(F : ℕ → Type)    -- functions. ℕ keeps track of arity.
(R : ℕ → Type)    -- relations

/-- Constants of a language are simply its 0-ary functions. -/
def lang.C (L : lang) : Type := L.F 0

def dense_linear_order: lang := {R := λ n : ℕ, if n=2 then unit else empty,
                                  F := function.const ℕ empty, C := empty}

/-- We now define some example languages. We start with the simplest
possible language, the language of pure sets. This language has no
functions, relations or constants.-/
def set_lang: lang := {F := function.const ℕ empty,
                       R := function.const ℕ empty}
                       
/-- Having defined a set_lang, we now use it to declare that lang is an
inhabited type.-/
instance lang.inhabited : inhabited lang := {default := set_lang}


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


/-- A dense linear ordering without endpoints is a language containg a
    single binary relation symbol < satisfying the following sentences:
-- 1. ∀x x < x;
-- 2. ∀x ∀y ∀z (x < y → (y < z → x < z));
-- 3. ∀x ∀y (x < y ∨ x = y ∨ y < x);
-- 4. ∀x ∃y x < y;
-- 5. ∀x ∃y y < x;
-- 6. ∀x ∀y (x < y → ∃z (x < z ∧ z < y)).

The  language contains exactly one relation: <, and no functions or constants-/
def DLO_lang : lang := {R := λ n : ℕ,                
                        if n = 2 then unit else empty,  -- one binary relation
                        ..set_lang}


/-! -----------------------------------------------------------------
-- 2. Structures and Examples
-- ----------------------------------------------------------------/


/-- We now define an L-structure to be interpretations of functions,
 relations and constants.

TODO: For now, we add in explicit interpretation of the constants as well
as (L.F 0). But in fact we should keep one or the other, not both.
-/
structure struc (L : lang) : Type 1 :=
(univ : Type)                                   -- universe/domain
(F (n : ℕ) (f : L.F n) : Func univ n)          -- interpretation of each function
(R (n : ℕ) (r : L.R n) : set (vector univ n))  -- interpretation of each relation
(C : L.C → univ)                               -- interpretation of each constant


/-- Type is a structure of the set language-/
def type_is_struc_of_set_lang {A : Type} : struc (set_lang) :=
 {univ := A,
  F := λ _ f, empty.elim f,
  R := λ _ r, empty.elim r,
  C := λ c, empty.elim c}


instance struc.inhabited {L : lang} : inhabited (struc L) :=
  {default := {univ := unit,  -- The domain must have at least one term
               F := λ _ _, mk_Func_of_total (function.const _ unit.star) unit.star,
               R := λ _ _, ∅,
               C := function.const _ unit.star}
  }



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



-- ∈ ℕ 
/-- We need to define a magma, because it looks like it is not defined
  in Mathlib.-/
class magma (α : Type) :=
(mul : α → α → α)

lemma free_magma_is_struc_of_magma_lang {A : Type} [magma A] :
  struc (magma_lang) :=
  {univ := A,
   F := by {intros n f,
            iterate {cases n, cases f}, -- if n=0,1
            exact magma.mul, -- if n=2
            cases f},        -- if n≥3
   R := λ _ r, empty.elim r,
   C := λ c, empty.elim c}


lemma semigroup_is_struc_of_semigroup_lang {A : Type} [semigroup A] :
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

  
/-- Ordered ring is a structure of the language of ordered rings
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
-/

/-- A type with linear order is a structure on dense-linear-order language.-/
def LO_is_struc_of_DLO_lang {A : Type} [linear_order A] : struc (DLO_lang) :=
  {univ := A,
   R := sorry,
   .. type_is_struc_of_set_lang}

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
(η : M.univ → N.univ)                        -- map of underlying domains
(η_inj : function.injective η)                -- should be one-to-one
(η_F : ∀ n f v,                              -- preserves action of each function
     η (app_vec (M.F (n+1) f) v) = app_vec (N.F (n+1) f) (vector.map η v))
(η_R : ∀ n r v,                              -- preserves each relation
     v ∈ (M.R n r) ↔ (vector.map η v) ∈ (N.R n r))
(η_C : ∀ c,                                   -- preserves each constant
     η (M.C c) = N.C c)


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
| app {n : ℕ} : term (n + 1) → term 0 → term (n)
open term

/-- We define an fterm (free-term) as begin similar to a term, but without
the `var` constructor.-/
inductive fterm : ℕ → Type
| con : L.C → fterm 0
| func {n : ℕ} : L.F n → fterm n
| app {n : ℕ} : fterm (n+1) → fterm 0 → fterm n
open fterm


/-- We define a coercion instance from fterm to term. This is to be understood
as "every fterm is also a term".  This is called "type-casting" in other
languages. Once we define the coercion, lean will put in the coercion maps wherever
needed to make the types agree.
-/
def fterm_to_term_coe {L : lang} : Π {n : ℕ}, fterm L n → term L n
| 0 (con c) :=  con c
| _ (func f) := func f
| _ (app t t₀) := app (fterm_to_term_coe t) (fterm_to_term_coe t₀)
instance fterm_to_term {n : ℕ} : has_coe (fterm L n) (term L n) := ⟨fterm_to_term_coe⟩

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
@[reducible] def number_of_vars {L : lang} : Π (n : ℕ), term L n → ℕ
| 0 (con c)    := 0
| 0 (var v)    := 1
| _ (func f)   := 0
| _ (app t t₀) := (vars_in_term  t ∪ vars_in_term t₀).card

set_option trace.inductive

/-- Recursively define term interpretation for variable-free terms. -/
def fterm_interpretation {L: lang} (M : struc L) :
  Π {n : ℕ} (t : fterm L n), Func M.univ n
| 0 (con c) := M.C c
| n (func f) := M.F n f
| _ (app t t₀) := (fterm_interpretation t) (fterm_interpretation t₀)


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


  /-- t = f(g(c, f(v₅))) is a term on language L1.-/
  def t₁ : fterm L1 0 := app (func f) (con c)            -- f(c)
  def t₂ : fterm L1 0 := app (app (func g) (con c)) t₁   -- g(c)(t₁)
  def t₃ : fterm L1 0 := app (func f) t₂                 -- f(t₂)
  def t : fterm L1 0 := app (func f)
                           $ app (app (func g) (con c))
                                 $ app (func f) (con c)

  #reduce fterm_interpretation M1 (func f)  -- f is interpreted as x ↦ 100x
  #reduce fterm_interpretation M1 (func g)  -- g is interpreted (x, y) ↦ x+y
  #reduce fterm_interpretation M1 (con c)   -- c is interpreted as (1 : ℕ)
  #eval fterm_interpretation M1 t₁     -- f(c) is interpreted as 100 
  #eval fterm_interpretation M1 t₂     -- g(c, t₁) is interpreted as 101
  #eval fterm_interpretation M1 t₃     -- f(g(c, f(c))) is interpreted as 10100
  #eval fterm_interpretation M1 t      -- same as t₃
  

end example_terms


/-! 4.2 Terms Substitution
    -----------------------/

/-- Simple example of a map where we substitute every variable
with exactly one term. A lemma will show if the term is variable
free, then the image of the function is variable free. Can be
generalized to subsitute each variable with its own term. -/
def term_sub {L : lang}(t' : term L 0) : Π n, term L n → term L n
| 0 (con c)    := con c
| 0 (var n)    := t'
| n (func f)   := func f
| n (app t t₀) := app (term_sub (n+1) t) (term_sub 0 t₀)

/--Alternative definition where we only allow the substitution to
occur over only one variable.-/

def term_sub_for_var {L : lang}(t' : term L 0)(k : ℕ) : 
  Π n, term L n → term L n
| 0 (con c)    := con c
| 0 (var n)    := if k = n then t' else var n
| n (func f)   := func f
| n (app t t₀) := app (term_sub_for_var (n+1) t) (term_sub_for_var 0 t₀)

open example_terms

def t₄ : term L1 0 := app (func f) (var 5) -- f(v₅)
def t₅ : term L1 0 := app (app (func g) (con c)) (var 4) -- g(c, v₄)
#reduce term_sub t₅ 0 t₄ -- f(g(c, v₄))
#reduce term_sub (var 3) 0 t₄ -- f(v₃)
#reduce term_sub_for_var (var 3) 4 0 t₄ -- f(v₅)
#reduce term_sub_for_var (var 3) 5 0 t₄ -- f(v₃)

/-! -----------------------------------------------------------------
-- 5. Formulas and Sentences
-- ----------------------------------------------------------------/


inductive formula (L : lang)
| t : formula
| f : formula
| eq  : term L 0 → term L 0 → formula
| rel : Π {n : ℕ}, L.R n → vector (term L 0) n → formula
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
notation `⊤'` : 110 := formula.t
notation `⊥'` : 110 := formula.f

/--Helper function for variables from list of terms-/

def vars_in_list {L : lang} : list (term L 0) → finset ℕ
|[] := ∅
|(t :: ts) := vars_in_term t ∪ vars_in_list ts

/-- Extracts set of variables from the formula-/

def vars_in_formula {L : lang}: formula L → finset ℕ 
| ⊤'                 := ∅
| ⊥'                 := ∅
| (t₁='t₂)           := vars_in_term t₁ ∪ vars_in_term t₂
| (formula.rel r ts) := vars_in_list (ts.to_list)
| (¬' ϕ)       := vars_in_formula ϕ
| (ϕ₁ ∧' ϕ₂)  := vars_in_formula ϕ₁ ∪ vars_in_formula ϕ₂
| (ϕ₁ ∨' ϕ₂)  := vars_in_formula ϕ₁ ∪ vars_in_formula ϕ₂
| (∃' v ϕ)    := vars_in_formula ϕ ∪ {v}
| (∀' v ϕ)    := vars_in_formula ϕ ∪ {v}

/-- A variable occurs freely in a formula if it is not quantified
over.-/
def is_var_free (n : ℕ) {L : lang}: formula L → Prop
| ⊤'                 := true
| ⊥'                 := true
| (t₁='t₂)           := true
| (formula.rel r ts) := true
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

/-! Examples of formulas and sentences.-/

namespace example_sentences
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

end example_sentences

/-! -----------------------------------------------------------------
-- 6. Satisfiability and Models
-- ----------------------------------------------------------------/

/-- Define an expanded language, given a struc M.

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


/-- We now interpret what it means for sentences to be true
    inside of our L-structures. -/
def models {L : lang} (M : struc L) : sentence L →  Prop
| ⟨⊤', h⟩           := true
| ⟨⊥', h⟩           := false
| ⟨(t₁ =' t₂), h⟩   := sorry
| ⟨formula.rel r ts, h⟩ := sorry
| ⟨¬' ϕ, h⟩             := sorry -- ¬models(ϕ)
| ⟨ϕ₁ ∧' ϕ₂, h⟩        := sorry -- models(ϕ₁) ∧ models (ϕ₂)
| ⟨ϕ₁ ∨' ϕ₂, h⟩        := sorry -- models(ϕ₁) ∨ models (ϕ₂)
| ⟨∃' v ϕ, h⟩          := sorry --∃(x ∈ M.univ) models (expanded_struc (L M) term_sub(x v ϕ))
| ⟨∀' v ϕ, h⟩          := sorry --∀(x ∈ M.univ) models (expanded_struc (L M) term_sub(x v ϕ))

