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

example {x : ℝ} : x ^ 2 + x - 6 = 0 ↔ x = -3 ∨ x = 2 := by
  constructor 
  · intros h 
    have h1 : x ^ 2 + x - 6 = (x + 3) * (x - 2) := by ring 
    rw [h1] at h 
    have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h
    obtain h2 | h2 := h2 
    · left 
      addarith [h2] 
    · right 
      addarith [h2] 
  · intros h 
    obtain h | h := h 
    · rw [h] 
      addarith 
    · rw [h] 
      addarith





