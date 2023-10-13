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

example : ∃! n : ℕ, ∀ a, n ≤ a := by
  use 0
  dsimp
  constructor

  . intro x
    extra       

  . intro x 
    intro h1
    have h2 := h1 0
    apply ge_antisymm
    extra
    exact h2