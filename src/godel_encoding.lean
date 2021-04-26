import model
import data.stream data.nat.prime

/--This is a (currently abandoned) attempt at defining a Godel Encoding.
    Godel Encoding/Numbering
    =======================

Section 5.5 in Lou's notes.
-/

-- Scott is going to attempt the impossible.
def godel_encoding (L : lang) : formula L → ℕ
| formula.tt :=  sorry
| formula.ff :=  sorry
| _ := sorry
--| formula.eq  := sorry
--| formula.rel := sorry
--| formula.neg := sorry
--| formula.and := sorry
--| formula.or  := sorry
--| formula.exi := sorry
--| formula.all := sorry


-- Proof omitted for now. [Schröder–Bernstein theorem?]
constant stream.primes : stream nat.primes

-- Alternatively, we could filter out the composite numbers.
#eval list.filter nat.prime (list.range 15)

-- ⟨a, b⟩ → 2^{a+1}*3^{b+1} and so on
#exit
def encoding1 : Π n, vector ℕ n → ℕ
| 0 v     := 1
| 1 v     := (stream.primes 0)^(v.nth 0 + 1)
| (n+1) v := (stream.primes n)^(v.head + 1) * encoding1 n (v.tail)

def func_number {L : lang} {n : ℕ} : L.F n → ℕ := sorry

def term_number {L : lang} : Π n, term L n → ℕ
| 0 (con c) := func_number c
| 0 (var v) := 2*v
| n (func f) := func_number f
| n (app t t₀) := term_number (n+1) t * term_number 0 t₀

-- ϕ₁ ∧ ϕ₂ := string_of_formula(∧) :: string_of_formula(ϕ₁) :: string_of_formula(ϕ₂)
