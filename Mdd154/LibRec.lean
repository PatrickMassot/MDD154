import Mdd154.Lib

protected theorem Nat.exists_eq_add_of_lt' {m n} (h : m < n) : ∃ k : Nat, n = k + m + 1 :=
  ⟨n - (m + 1), by grind⟩

addAnonymousFactSplittingLemma Nat.exists_eq_add_of_le
addAnonymousFactSplittingLemma Nat.exists_eq_add_of_le'
addAnonymousFactSplittingLemma Nat.exists_eq_add_of_lt
addAnonymousFactSplittingLemma Nat.exists_eq_add_of_lt'

axiom foo (u : ℕ → ℝ) (h : ∀ n, u (n + 1) ≥ u n) : u est croissante

addAnonymousFactSplittingLemma foo

def suite_rec (f : ℝ → ℝ) (u₀ : ℝ) : ℕ → ℝ
| 0 => u₀
| (n + 1) => f (suite_rec f u₀ n)

