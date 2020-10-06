import tactic -- this shows that mathlib is getting imported correctly.
import data.real.basic
-- This is a file for running random snippets of lean code
/-this is a docstring.

Write longer comments like this.-/

-- We can define functions

-- We can define types. And then terms of that types.
-- Inductive types
-- Structures (a special type of inductive type).



/-! Today we will be talking about Recursion.
    -----------------------------------------

Functional programming languages do not have loops (for and while).
Here we do everything with recursion instead.

Recursion = a function calling itself (with some different arguments).

-/
namespace recursion -- we open a namespace so as to avoid name clashes

open nat

def add : ℕ → ℕ → ℕ      -- here m is "unbundled".
| m 0        := m
| m (succ n) := succ (add m n)


def add' (m : ℕ) : ℕ → ℕ  -- here m is "bundled".
| zero     := m
| (succ n) := succ (add' n)

#check add
#check add'
#reduce add 100 200
#eval add 100 200


def fac : ℕ → ℕ
| 0       := 1
| (n + 1) := (n + 1) * fac n


def fac1 : ℕ → ℕ
| 0 := 1
| n := sorry -- n * fac' (n - 1)  -- This fails!

/-! Factorial using accumulator (more efficient).
This uses tail recursion.
-/
def go : ℕ → ℕ → ℕ
| 0 acc        := acc
| (n + 1) acc := go n ((n+1)*acc)
-- This is called "tail" recursion because we make a single recursive
-- call at the very end in the function go.
def fac2 (n : ℕ) := go n 1

#eval fac2 4


/-! Another example to illistrate tail recursion.
Note: good resource on tail recursion is Computerphile's video on tail recursion:
[[https://youtu.be/_JtPhF8MshA]].

First we define fib without tail recursion.-/
def fib : ℕ → ℕ  -- compute the n-th Fibonacci number.
| 0       := 0
| 1       := 1
| (n + 2) := fib (n + 1) + fib n

#eval fib 15  -- don't use big numbers. Not very efficient.

/-Now we try to make this more efficient using tail recursion.-/
def go' : ℕ → ℕ → ℕ → ℕ
|  0    a b := a
|  1    a b := b
| (n+1) a b := go' n b (a+b)
def fib' (n : ℕ) : ℕ := go' n 0 1

#eval fib' 15

def length {α : Type} : list α → ℕ
| []        := 0
| (x :: xs) := succ $ length xs

#eval length [1, 2, 12]

-- Sum the elements in a list
def sum {α : Type} [has_add α] [has_zero α] : list α → α
| [] := 0
| (x :: xs) := x + sum xs

-- Multiply the elements in a list
def mul {α : Type} [has_mul α] [has_one α] : list α → α 
| [] := 1
| (x :: xs) := x * mul xs

#eval mul [7, 9, 2] -- output: 126

def max {α : Type} [decidable_linear_order α]: list α → α
| []        := [].minimum
| (x :: xs) := if x < max xs then max xs else x

#print decidable_linear_order
#eval max [14, 17]


def max' {α : Type} [decidable_linear_order α] : list α → option α
| []        := none
| (x :: xs) := match (max' xs) with
               | none := x
               | some m := if x < m then m else x
               end

#eval max [1, 3, 20, 5, 10]
#eval max' [1, 3, 20, 5, 10]

end recursion


