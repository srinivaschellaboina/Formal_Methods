import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel

example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  obtain ⟨a, ha⟩ := h
  have H := le_or_gt t 1
  obtain h1 | h1 := H
  · have hat : a * t + 1 ≤ a + t := by rel [h1]
    contradiction
  · apply ne_of_gt
    exact h1
