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

example {a b : ℝ} (h : ∀ x, x ≥ a ∨ x ≤ b) : a ≤ b := by
  have H := h ((a+b)/2) 
  obtain H1 | H2 := H 
  calc 
    a   ≤ (a+b)/2 := by rel [H1]
    _ = 0.5*a + 0.5*b := by ring
    _ ≤ b := by rel [H]
     








