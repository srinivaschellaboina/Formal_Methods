import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.Prime
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel

example : ∃ c : ℝ, ∀ x y, x ^ 2 + y ^ 2 ≤ 4 → x + y ≥ c := by
  use 0
  intros x y h
  calc
    0 = x + (-x) := by ring
    _ ≤ x + y := by {
      by_cases hy : y ≥ 0,
      { exact add_le_add_left hy x },
      { push_neg at hy,
        have h1 : y^2 ≤ x^2,
        { have h2 : x^2 + y^2 ≤ 4 := h,
          exact le_of_add_le_add_left h2 },
        have h3 : abs y ≤ abs x := by { rw [abs_of_nonpos hy, abs_of_nonneg (le_of_sq_le_sq (le_of_lt hy) h1)], exact le_refl _ },
        exact add_le_add_left (neg_le_of_neg_le h3) x }
    }
    _ = x + y : by ring




