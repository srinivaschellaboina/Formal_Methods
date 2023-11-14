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

namespace Nat

example (p : ℕ) (h : Prime p) : p = 2 ∨ Odd p := by
  dsimp [Prime] at h 
  obtain ⟨h1,h2⟩ := h
  have h3 := h2 2 
  by_cases 2 ∣ p
  · left 
    have := h3 h 
    simp at this 
    symm; apply this 
  · right 
    rw [Nat.odd_iff_not_even p] 
    dsimp [Even] 
    dsimp [(.∣.)] at h 
    apply h
