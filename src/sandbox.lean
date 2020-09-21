import tactic -- this shows that mathlib is getting imported correctly.
import data.real.basic
-- This is a file for running random snippets of lean code
/-this is a docstring.

Write longer comments like this.-/

-- We can define functions

-- We can define types. And then terms of that types.
-- Inductive types
-- Structures (a special type of inductive type).



/-! Example showing how we can define a case-by-case function on fin n.-/

def crazy_arity : fin 3 → ℕ
| ⟨0, _⟩ := 3
| ⟨1, _⟩ := 1
| ⟨2, _⟩ := 2
| _     := 1000


def crazy_arity2 : fin 3 → ℕ :=
begin
  intro a₀,
  cases a₀ with a₁ _,
  cases a₁ with a₂ _,
    { use 3},
  cases a₂ with a₃ _,
    { use 1},
  cases a₃ with a₄ _,
    {use 2},
  use 1000,
end


lemma the_two_defs_are_equal (a : fin 3) :
  crazy_arity a = crazy_arity2 a :=
begin
  cases a,
  iterate 3 {cases a_val, refl},
  refl,
end

