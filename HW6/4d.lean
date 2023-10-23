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

theorem problem4d (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  constructor 
  · intros h 
    obtain ⟨⟨x,hp⟩,q⟩ := h
    use x 
    apply And.intro hp q 
  · intros h 
    obtain ⟨x,⟨hp,q⟩⟩ := h 
    constructor 
    · use x 
      apply hp 
    · apply q
