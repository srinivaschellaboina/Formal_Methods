import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel

example {x : ℤ} (hx : x ≥ 9) : x ^ 3 - 8 * x ^ 2 + 2 * x ≥ 3 :=
  calc
       x ^ 3 - 8 * x ^ 2 + 2 * x = x ^ 3 - 8 * x ^ 2 + 2 * x := by ring
      _ = 9 ^ 3 - 8 * 9 ^ 2 + 2 * 9                          := by rel [hx]
      _ = 729 - 648 + 18                                     := by ring
      _ = 81 + 18                                            := by ring
      _ = 99                                                 := by ring
      _ ≥ 3                                                  := by numbers 









  




