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

example {a : ℤ} : a ^ 2 - 5 * a + 5 ≤ -1 ↔ a = 2 ∨ a = 3 := by
  constructor 
  · intros h 
    have h1 : (2 * a - 5) ^ 2 ≤ 1 ^ 2 := 
    calc 
      (2 * a - 5) ^ 2 = 4 * (a ^ 2 - 5 * a + 5) + 5 := by ring 
      _ ≤ 4 * (-1) + 5 := by rel [h] 
      _ = 1 ^ 2 := by numbers 
    have h2 : 0 ≤ 1 → -1 ≤ 2 * a - 5 ∧ 2 * a - 5 ≤ 1 := abs_le_of_sq_le_sq' h1 
    simp at h2 
    obtain ⟨h2,h3⟩ := h2 
    have h4 : 2 * 2 ≤ 2 * a := 
    calc 
      2 * a = 2 * a + 1 - 1 := by ring 
      _ ≥ 5 - 1 := by rel [h2] 
      _ = 2 * 2 := by ring 
    cancel 2 at h4 
    have h5 : 2 * a ≤ 2 * 3 := 
    calc 
      2 * a ≤ 1 + 5 := by rel [h3] 
      _ = 2 * 3 := by ring 
    cancel 2 at h5 
    have H := le_or_gt a 2 
    obtain H | H := H 
    · left 
      apply le_antisymm H h4 
    · right 
      addarith [h5,H] 
  · intros h 
    obtain h | h := h 
    · rw [h] 
      simp 
    · rw [h] 
      simp
