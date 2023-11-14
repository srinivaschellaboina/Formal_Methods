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

example : ∃! x : ℚ, ∀ a, a ≥ 1 → a ≤ 3 → (a - x) ^ 2 ≤ 1 := by
  use 2 
  dsimp 
  constructor 
  · intros a ha1 ha3 
    simp 
    dsimp [abs] 
    simp 
    constructor 
    · calc 
        a ≤ 3 := ha3  
        _ = 1 + 2 := by numbers 
    · calc 
        1 + a ≥ 1 + 1 := by rel [ha1] 
        _ = 2 := by numbers 
  · intros y h
    have h1 : 1 ≥ 1 → 1 ≤ 3 → (1 - y) ^ 2 ≤ 1 := h 1 
    have h1' : (1 - y) ^ 2 ≤ 1 := by 
      apply h1 
      simp 
      simp 
    have h3 : 3 ≥ 1 → 3 ≤ 3 → (3 - y) ^ 2 ≤ 1 := h 3 
    have h3' : (3 - y) ^ 2 ≤ 1 := by 
      apply h3 
      simp 
      simp 
    have hAbove : (y - 2) ^ 2 ≤ 0 := 
    calc 
      (y - 2) ^ 2 = ((1 - y) ^ 2 + (3 - y) ^ 2 - 2) / 2 := by ring 
      _ ≤ (1 + 1 - 2) / 2 := by rel [h1',h3'] 
      _ = 0 := by numbers 
    have hBelow : 0 ≤ (y - 2) ^ 2 := by extra 
    have hy : (y - 2) ^ 2 = 0 := by apply le_antisymm hAbove hBelow 
    simp at hy
    calc 
      y = y - 2 + 2 := by ring 
      _ = 0 + 2 := by rw [hy] 
      _ = 2 := by numbers
