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

example {p : ℕ} (hp : 2 ≤ p) (H : ∀ m : ℕ, 1 < m → m < p → ¬m ∣ p) : Prime p := by
  constructor
  · apply hp 
  intro m hmp
  have hp' : 0 < p := by extra
  have h1m : 1 ≤ m := Nat.pos_of_dvd_of_pos hmp hp'
  obtain hm | hm_left : 1 = m ∨ 1 < m := eq_or_lt_of_le h1m
  · ---for `m = 1`
    left
    addarith [hm]
  ---for `1 < m`
  . have h2:= H m 
    have h3 := h2 hm_left
    have h4 : m ≤ p := by
      apply Nat.le_of_dvd
      extra
      exact hmp
    obtain h6 | h7 : m = p ∨ m < p := eq_or_lt_of_le h4
    right
    exact h6
    
    have h5 := h3 h7
    contradiction