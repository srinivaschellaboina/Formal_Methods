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
import Library.Tactic.Use



example : ∀ x : ℝ, x ^ 3 + 3 * x ≥ 7 * x ^ 2 + 12 := by
  intro x,
  have h1 : x ^ 3 + 3 * x - (7 * x ^ 2 + 12) ≥ 0,
    dsimp,
    rw [←sub_eq_add_neg],
    have h2 : x ^ 3 - 7 * x ^ 2 + (3 * x - 12) ≥ 0,
      ring,
    apply add_nonneg,
    { apply pow_nonneg (le_of_lt x.lt_trivial) 3 },
    { apply mul_nonneg (le_of_lt x.lt_trivial) (add_nonneg (mul_nonneg (le_of_lt x.lt_trivial) (le_of_lt x.lt_trivial)) (neg_nonneg.mpr (by linarith))),
      apply sub_nonneg_of_le,
      ring_nf,
      rw [add_comm, sub_add_cancel],
      exact h2 },
  interval_cases x using [h1],
  all_goals { ring },
