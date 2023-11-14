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

example {k : ℕ} : k ^ 2 ≤ 6 ↔ k = 0 ∨ k = 1 ∨ k = 2 := by
  constructor 
  · intros h 
    have H1 := le_or_gt k 0
    obtain H1 | H1 := H1 
    · left 
      simp at H1 
      apply H1 
    · right 
      have H2 := le_or_gt k 1 
      obtain H2 | H2 := H2 
      · left 
        have H3 : k ≥ 1 := by addarith [H1] 
        apply le_antisymm H2 H3 
      · right 
        have H3 : k ≥ 2 := by addarith [H2] 
        have H4 : ¬(k ≥ 3) := by 
          intros H5 
          have H6 : 3 * 2 ≥ 3 * k := 
          calc 
            3 * 2 = 6 := by ring 
            _ ≥ k ^ 2 := by rel [h] 
            _ = k * k := by ring 
            _ ≥ 3 * k := by rel [H5] 
          cancel 3 at H6 
          have H7 : k = 2 := le_antisymm H6 H3 
          addarith [H5,H7] 
        simp at H4 
        addarith [H3,H4] 
  · intros h 
    obtain h1 | h2 | h3 := h 
    · rw [h1] 
      numbers 
    · rw [h2] 
      numbers 
    · rw [h3] 
      numbers
