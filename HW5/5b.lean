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

example : ∃! x : ℚ, 4 * x - 3 = 9 := by
  use 3 
  dsimp 
  constructor 
  · numbers 
  · intros y h 
    have h' : 4 * y = 4 * 3 := 
    calc 
      4 * y = 4 * y - 3 + 3 := by ring 
      _ = 9 + 3 := by rw [h] 
      _ = 4 * 3 := by numbers 
    cancel 4 at h'
