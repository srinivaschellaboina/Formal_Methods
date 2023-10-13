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
  numbers 

  intro x
  intro h1
  calc
    x = (4 * x) / 4 := by ring 
    _ = (4 * x - 3 + 3) / 4 := by ring 
    _ = (9 + 3) / 4 := by rw[h1]
    _ = 3 := by numbers