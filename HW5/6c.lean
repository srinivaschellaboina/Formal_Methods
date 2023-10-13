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

example {x y : ℝ} (n : ℕ) (hx : 0 ≤ x) (hn : 0 < n) (h : y ^ n ≤ x ^ n) :
    y ≤ x := by
  have h1 := lt_or_ge x y
  obtain h2|h3 := h1
  . have h3: x^n < y^n := by 
      calc 
        x^n = x ^n := by ring
        _  < y^n := by rel[h2]
    have h4: ¬ y^n ≤ x^n := by
      apply not_le_of_gt
      apply h3
    contradiction

  . addarith[h3]