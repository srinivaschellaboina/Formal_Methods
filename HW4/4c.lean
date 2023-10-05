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

example {n : ℤ} (hn : Even n) : Odd (n ^ 2 + 2 * n - 5) := by
  dsimp [Even] at *
  obtain ⟨l, hl⟩ := hn
  use 2*l^2 +2*l -3
  calc
    n^2 + 2*n -5 = (l+l)^2 + 2*(l+l) -5 := by rw[hl]
    _ = (2*l)^2 + 2*(2*l)-5 := by ring
    _ = 4*l^2 + 4*l - 5 :=by ring
    _ = 2*(2*l^2+2*l-3) + 1 := by ring 
