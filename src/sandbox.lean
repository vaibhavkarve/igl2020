import tactic -- this shows that mathlib is getting imported correctly.
import data.real.basic
-- This is a file for running random snippets of lean code
/-this is a docstring.

Write longer comments like this.-/

-- We can define functions

-- We can define types. And then terms of that types.
-- Inductive types
-- Structures (a special type of inductive type).

-- Just the natural numbers
inductive mynat : Type
| O : mynat          -- zero
| S : mynat → mynat -- successor function

ℕ vs mynat

O
S(O) = 1
S(S(O))


--- [1, 2, 3] : list ℕ
inductive mylist : Type
| nil : mylist                  --- this is the empty list
| cons : ℕ → mylist → mylist  --- cons means list-constructor
-- [] = nil 
-- [] : mylist
-- cons 1 nil : mylist         == [1]
-- cons 2 (cons 1 nil) : mylist  == [2, 1]



inductive mybool : Type
| tt : mybool
| ff : mybool
-- Difference between Types, terms, constructors
-- mybool.tt
-- mybool.ff

def f : mybool := mybool.ff


inductive weekday : Type
| monday : weekday
| tuesday : weekday
| wednesday : weekday


structure graph :=
(V : Type)
(adj : V → V → Prop)
(adj_symm (v w : V) : adj v w → adj w v)

-- inductive graph'
-- | mk (V : Type) (adj : V → V → Prop) (adj_symm (v w : V) : adj v w → adj w v)

-- Inductive types with a single constructor are better represented as structures.

-- We use the colon to denote type.
-- 1 : ℕ
-- {1, 2} : set ℕ
-- adj_symm (v w : V) : adj v w → adj w v
-- We can also read this as "adj_symm v w" is a **proof** of the proposition written above.

-- Curry-Howard Isomorphism
----------------------------
-- Terms are proofs
-- Types are theorems

-- Lean commands we should know:
-- 1. #check (ask Lean what the type of an expression is)
-- 2. #print (look at definition of any object in lean)
-- 3. library_search

#check (3.5 : ℚ)
#check (3.5 : ℝ)

example (l : list ℕ) : ℕ := sizeof l
#print sizeof


#check (set ℕ)
-- This is the type of all subsets of ℕ
#check set

example : set ℕ := {1, 2}
example : set ℕ := ∅ -- \empty

-- Usual math uses Set theory.
-- Lean uses Type theory (but also understands sets).
-- Prop is the type of all propositions/facts.
def example_adj : bool → bool → Prop
| _ _ := true

def myfavgraph : graph := ⟨bool, example_adj, _⟩  --- angled brackets can be typed as \< and \>
-- What are the vertices of this graph?
-- {tt, ff}
-- What are the edges of this graph?
-- tt::tt , tt::ff, ff::tt, ff::ff

example : ℕ := by library_search
