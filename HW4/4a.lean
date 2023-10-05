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

example {n : ℤ} (hn : Odd n) : Odd (7 * n - 4) := by
  -- Obtain k such that n = 2k + 1 (using the definition of odd)
  obtain ⟨k, rfl⟩ := hn;
  -- Express 7n - 4 in terms of k
  have h : 7 * (2 * k + 1) - 4 = 2 * (7 * k + 1) + 1 := by 
    calc 
      7 * (2 * k + 1) - 4 = 14 * k + 7 - 4 := by ring
      _ = 14 * k + 3 := by addarith
      _ = 2 * (7 * k + 1) + 1 := by ring;
  -- Use the definition of odd to conclude
  use 7 * k + 1;
  exact h
