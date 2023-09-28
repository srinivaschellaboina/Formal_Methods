import Mathlib.Data.Real.Basic
import Library.Theory.Comparison
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use

example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x :=
by_cases 
  (λ h : x < 0 => 
    use 0, 
    apply ne_of_gt, 
    exact gt.trans (pow_pos zero_lt_two) h)
  (λ h : ¬ x < 0 =>
    by_cases 
      (λ h1 : x = 0 => 
        use 1, 
        rw h1, 
        apply ne_of_gt, 
        exact zero_lt_one^2)
      (λ h1 : ¬ x = 0 => 
        have h2 : x > 0 := le_antisymm (not_lt.mp h) (ne_of_lt (lt_of_le_of_ne (le_of_not_gt h) h1)), 
        use x + 1, 
        apply ne_of_gt, 
        exact lt.trans h2 (lt_add_one x)))