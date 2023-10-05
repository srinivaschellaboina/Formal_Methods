import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y + 2 * y) := by
  obtain ⟨a, rfl⟩ := hx;
  obtain ⟨b, rfl⟩ := hy;
  have h : (2 * a + 1) * (2 * b + 1) + 2 * (2 * b + 1) = 2 * (2 * a * b + 3 * b + a + 1) + 1 := by 
    calc 
      (2 * a + 1) * (2 * b + 1) + 2 * (2 * b + 1) = 4 * a * b + 2 * a + 2 * b + 1 + 4 * b + 2 := by ring
      _ = 2 * (2 * a * b + 3 * b + a + 1) + 1 := by ring;
  use 2 * a * b + 3 * b + a + 1;
  exact h
