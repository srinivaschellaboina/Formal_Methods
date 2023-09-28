import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel

example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p + q) / 2
  have h1 : p < (p + q) / 2 := 
    calc
      p = (p + p) / 2 := by ring
      _ < (p + q) / 2 := by rel [h]
  have h2 : (p + q) / 2 < q :=
    calc
      (p + q) / 2 < (q + q) / 2 := by rel [h]
      _ = q := by ring
  exact ⟨h1, h2⟩