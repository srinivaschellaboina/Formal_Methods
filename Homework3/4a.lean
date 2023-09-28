import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel

example {t : ℝ} (h : ∃ x : ℝ, x * t < 0) : t ≠ 0 := by
  obtain ⟨x, hxt⟩ := h
  have H := le_or_gt x 0
  obtain hx | hx := H
  · have hxt' : 0 < (-x) * t := by addarith [hxt]
    have hx' : 0 ≤ -x := by addarith [hx]
    cancel -x at hxt'
    apply ne_of_gt
    exact hxt'
  · have hxt' : 0 < -(x * t) := by addarith [hxt]
    have hx' : 0 < x := by addarith[hx]
    have : t = -(-t) := by ring
    apply ne_of_lt
    exact lt_of_neg_lt_neg hx'