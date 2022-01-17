import tactic

-- Local imports
import lang

/-!
# struc.lean

In this file, we define structures, substructures, embeddings, and
isomorphisms between two structures.

## Tags

model theory, structures
-/


/-! ## Structures -/


/-- We now define an L-structure to be mapping of functions, relations and
 constants to appropriate elements of a domain/universe type.-/
structure struc (L : lang) : Type 1 :=
(univ : Type)                       -- universe/domain
[univ_inhabited: inhabited univ]    -- we assume the universe is always inhabited
(F {n : ℕ+} (f : L.F n) : Func univ n)        -- interpretation of each function
(R {n : ℕ+} (r : L.R n) : set (vector univ n))-- interpretation of each relation
(C : L.C → univ)                              -- interpretation of each constant


namespace struc
instance inhabited {L : lang} : inhabited (struc L) :=
  {default := {univ := unit,  -- The domain must have at least one term
               F := λ _ _, Func.mk_of_total (function.const _ unit.star),
               R := λ _ _, ∅,
               C := function.const L.C unit.star}
  }

/-- The cardinality of a structure is the cardinality of its domain.-/
def card {L : lang} (M : struc L) : cardinal := cardinal.mk M.univ

end struc

/- Define an expanded language, given a struc M.

Idea: For every element of M.univ, we will add a new constant to the
language.

In Lou's book (more general): we start instead with C ⊂ M.univ, and then add
only elements of C as constants to the language. -/
@[reducible] def struc.expanded_lang {L : lang} (M : struc L) : lang :=
  {C := M.univ ⊕ L.C, .. L}

/-- Define expanded structures. -/
def struc.expanded_struc {L: lang} (M : struc L) : struc M.expanded_lang :=
  {C := λ c, sum.cases_on c id M.C,
   .. M}


local notation f^M := M.F f -- f^M denotes the interpretation of f in M.
local notation r`̂`M : 150 := M.R r -- r̂M denotes the interpretation of r in
                              -- M. (type as a variant of \^)

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


namespace embedding
/-- We argue that every structure has an embedding, namely, the embedding
to itself via the identity map.-/
instance inhabited {L : lang} {M : struc L} : inhabited (embedding M M) :=
  {default := {η := id,
               η_inj := function.injective_id,
               η_F := by simp,
               η_R := by simp,
               η_C := λ _, rfl}}

/-- If η: M → N is an embedding, then the cardinality of N is at least the
  cardinality of M.-/
lemma le_card {L : lang} (M N : struc L) (η : embedding M N) :
  M.card ≤ N.card := cardinal.mk_le_of_injective η.η_inj

end embedding

/-- A bijective embedding between two `L`-structures is called an isomorphism.
We use the `equiv` type, denoted `M.univ ≃ N.univ` to capture the type of
bijective maps bundled with inverse maps.
-/
structure isomorphism {L: lang} (M N : struc L) extends (embedding M N) : Type
:=
(equiv : M.univ ≃ N.univ)
(eq_equiv_η : η = equiv.to_fun)


/-- We argue that every structure has an isomorphism to itself via the identity
  map.-/
instance isomorphism.inhabited {L : lang} {M : struc L} :
inhabited (isomorphism M M) :=
  {default := {equiv := equiv.refl _,
               eq_equiv_η := rfl,
               .. default (embedding M M)}}




/-- If `M ⊆ N` and the inclusion map is an `L`-embedding, we say either
  that `M` is a substructure of `N` or that `N` is an extension of `M`.

Note: the other conditions for `η` being an `L`-embedding follow from the
definition of `coe`.
-/
structure substruc {L : lang} (N : struc L) : Type :=
(univ : set N.univ)                        -- a subset of N.univ
[univ_inhabited : inhabited univ]          -- the subset should have a default
(univ_invar_F :  ∀ (n : ℕ+) (f : L.F n) (v : vector univ n),
                 f^N ⊗ (v.map coe) ∈ univ)  -- univ is invariant over f
(univ_invar_C : ∀ (c : L.C), N.C c ∈ univ) -- univ contains all constants


variables (L : lang) (M : struc L) (S₁ S₂ : substruc M)


namespace substruc
/- We can show that the intersection of 2 substructures is
a substructure. -/
def intersection {L : lang} {M : struc L}
 (S₁ S₂ : substruc M) [inhabited ↥(S₁.univ ∩ S₂.univ)] : substruc M :=
 {univ := S₁.univ ∩ S₂.univ,
  univ_invar_F := λ n f v', by {norm_num, split,
                                have v : vector S₁.univ n,
                                fconstructor,
                                have v'' := v'.val,
                                have x := S₁.univ_invar_F n f,
                                unfold_coes,
                                repeat {sorry}},
  univ_invar_C := λ c, ⟨S₁.univ_invar_C c, S₂.univ_invar_C c⟩}

/-- A substructure is finite if it has only finitely many domain elements.-/
class fin_substruc {L : lang} {N : struc L} (S : substruc N) :=
(finite : set.finite S.univ)


/-- Every substruc is a struc.-/
instance has_coe {L: lang} {M : struc L} :
  has_coe (substruc M) (struc L)
:= {coe := λ S, {univ := S.univ,
                 F := λ n f, (f^M).mapn coe n,
                 R := λ _ r v, v.map coe ∈ (r̂M),
                 C := λ c, ⟨M.C c, S.univ_invar_C c⟩,
                 univ_inhabited := S.univ_inhabited}}

/- For a given structure N on a language L, an inhabited substructure can
   be generated from any subset of N.univ via substruc.closure -/
instance inhabited {L : lang} {N : struc L} {α : set N.univ} :
  inhabited (substruc N) :=
 {default := {univ := set.univ,
              univ_invar_F := by simp,
              univ_invar_C := by simp,
              univ_inhabited := ⟨⟨@default N.univ N.univ_inhabited, by simp⟩⟩}}
end substruc
