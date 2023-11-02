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

example (P Q : Prop) : ¬ (P → Q) ↔ (P ∧ ¬ Q) := by
  constructor
  · intros h1
    by_cases P ∧ ¬Q
    · apply h
    · apply False.elim
      apply h1
      intros p
      rw [not_and_or] at h
      obtain h | h := h
      · contradiction
      · rw [not_not] at h
        apply h
  · intros h1 h2
    obtain ⟨p,nq⟩ := h1
    have q : Q := h2 p
    contradiction
