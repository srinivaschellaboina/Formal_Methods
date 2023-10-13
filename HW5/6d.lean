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

example (p : ℕ) (h : Prime p) : p = 2 ∨ Odd p := by
  dsimp [Prime] at *
  obtain ⟨h1,h2⟩ := h
  have h1 : p ≤ 2 ∨ p ≥ 3 := by apply le_or_succ_le p 2
  obtain h3|h4:= h1 
  . left
    apply le_antisymm h3 h1
  . right
    obtain h5|h6 := Nat.even_or_odd p
    . dsimp [Nat.Even] at h5
      obtain ⟨k,hk⟩ := h5
      have h5:= h2 2
      have h6: 2∣ p := by 
        use k
        apply hk
      have h5 := h5 h6
      obtain h7|h8 := h5
      . contradiction
      . have h9: 2 ≥ 3 := by 
          calc
            2 = p := by apply h8
            _ ≥ 3 := by rel[ h4]
        contradiction
    . apply h6