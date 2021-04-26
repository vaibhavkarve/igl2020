import tactic

/-!
# func.lean

In this file, we define functions of arity `(n : ℕ)` and their API.

## Tags

functions, arity
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

namespace Func
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
instance inhabited {α : Type} [inhabited α] : inhabited (Funcs α) :=
 {default := ⟨0, default α⟩}


/-- Define a constructor for Func. It takes in a total function `f` and turns
it into a partial function of the same arity.

1. This constructor can only make functions of arity ≥ 1.
2. This constructor makes a recursive call to itself. -/
def mk_of_total {α : Type} : Π {n : ℕ+}, (vector α n → α) → Func α n
| ⟨0, _⟩ f := by linarith
| ⟨1, _⟩ f := λ a, f ⟨[a], by norm_num⟩ -- this produces a 1-ary func
| ⟨n+2, h⟩ f := λ a, @mk_of_total ⟨n+1, by linarith⟩ (λ v, f (a ::ᵥ v)) -- an (n+1)-ary function


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
end Func

-- Under this notation, if `(f : Func α n)` and `(v : vector α n)`, then `(f ⊗
-- n)` denotes the value in `α` obtained by feeding the `n` elements of `v` to
-- `f`.
infix `⊗` : 70 := Func.app_vec

namespace Func
/-- Apply a Func to a function on `fin n`.-/
def app_fin {α : Type} {n : ℕ+} (f : Func α n) (v : fin n → α) : α :=
  f ⊗ (vector.of_fn v)


def map {n : ℕ+} {α : Type} {A : set α} (F : Func α n) {f : A → α} :
 (∀ v : vector A n, F ⊗ v.map f ∈ A) → Func A n :=
 λ h, mk_of_total (λ v, ⟨F ⊗ (v.map f), h v⟩)

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

end Func
