import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel

example {m : ℤ} (h : ∃ a : ℤ, 2 * a = m) : m ≠ 5 := by
  obtain ⟨a, ha⟩ := h
  intro hm
  have h1 : m = 2 * a := ha
  have h2 : m = 5 := hm
  have h3 : 2 * a = 5 := by rel [h1, h2]
  have h4 : a ≠ 5 / 2 := by numbers
  exact h4 (eq_div_of_mul_eq h3)