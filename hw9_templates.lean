import Mathlib.Data.Real.Basic
import Library.Theory.Parity
import Library.Theory.Comparison
import Library.Theory.Prime
import Library.Tactic.Induction
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Use
import Mathlib.Tactic.GCongr
import Library.Tactic.Cancel

notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r

def B : ℕ → ℚ
  | 0 => 0
  | n + 1 => B n + (n + 1 : ℚ) ^ 2

/- 2 points -/
theorem problem4a (n : ℕ) : B n = n * (n + 1) * (2 * n + 1) / 6 := by
  sorry

def S : ℕ → ℚ
  | 0 => 1
  | n + 1 => S n + 1 / 2 ^ (n + 1)

/- 3 points -/
theorem problem4b (n : ℕ) : S n = 2 - 1 / 2 ^ n := by
  sorry

/- 3 points -/
theorem problem4c (n : ℕ) : S n ≤ 2 := by
  sorry

def factorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

notation:10000 n "!" => factorial n

/- 3 points -/
theorem problem4d (n : ℕ) : (n + 1) ! ≤ (n + 1) ^ n := by
  sorry

def q : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | n + 2 => 2 * q (n + 1) - q n + 6 * n + 6

/- 3 points -/
theorem problem5a (n : ℕ) : q n = (n:ℤ) ^ 3 + 1 := by
  sorry

def r : ℕ → ℤ
  | 0 => 2
  | 1 => 0
  | n + 2 => 2 * r (n + 1) + r n

/- 3 points -/
theorem problem5b : forall_sufficiently_large n : ℕ, r n ≥ 2 ^ n := by
  sorry

/- 3 points -/
theorem problem5c (n : ℕ) (hn : 0 < n) : ∃ a x, Odd x ∧ n = 2 ^ a * x := by
  sorry
