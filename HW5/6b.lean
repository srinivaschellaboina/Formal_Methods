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

example {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h_pyth : a ^ 2 + b ^ 2 = c ^ 2) : 3 ≤ a := by
  obtain hneg | hpos : a ≤ 2 ∨ 2 < a := le_or_lt a 2 
  · obtain b_le_1 | b_gt_1 := le_or_lt b 1 
    · have h : c ^ 2 < 3 ^ 2 := 
      calc 
        c ^ 2 = a ^ 2 + b ^ 2 := by rw [h_pyth] 
        _ ≤ 2 ^ 2 + 1 ^ 2 := by rel [hneg,b_le_1] 
        _ < 3 ^ 2 := by numbers 
      cancel 2 at h 
      interval_cases a 
      interval_cases b 
      interval_cases c <;> contradiction 
      interval_cases b 
      interval_cases c <;> contradiction 
    · have b_ge_2 : b ≥ 2 := b_gt_1 
      have fact : b ^ 2 < c ^ 2 := 
      calc 
        b ^ 2 < a ^ 2 + b ^ 2 := by extra 
        _ = c ^ 2 := by rw [h_pyth] 
      cancel 2 at fact 
      have factplus1 : b + 1 ≤ c := fact 
      have := 
      calc 
        c ^ 2 = a ^ 2 + b ^ 2 := by rw [h_pyth] 
        _ ≤ 2 ^ 2 + b ^ 2 := by rel [hneg] 
        _ = b ^ 2 + 2 * 2 := by ring 
        _ ≤ b ^ 2 + 2 * b := by rel [b_ge_2] 
        _ < b ^ 2 + 2 * b + 1 := by extra 
        _ = (b + 1) ^ 2 := by ring 
      cancel 2 at this 
      have that : ¬(c < b + 1) := by 
        push_neg 
        apply factplus1 
      contradiction 
  apply hpos
