import tactic
import set_theory.cardinal

-- Local imports
import func

/-!
# lang.lean

In this file, we define
- languages

## Tags

languages, model theory
-/

/-! ## Languages -/

/-- A language is given by specifying functions, relations and constants
along with the arity of each function and each relation.-/
structure lang : Type 1 :=
(F : ℕ+ → Type)    -- functions. ℕ keeps track of arity.
(R : ℕ+ → Type)    -- relations
(C : Type)         -- constants


namespace lang
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
instance inhabited : inhabited lang := {default := DLO_lang}


def card (L : lang) : cardinal :=
  cardinal.sum (cardinal.mk ∘ L.F) + cardinal.sum (cardinal.mk ∘ L.R)

end lang
