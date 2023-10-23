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

theorem problem4a {P Q : α → Prop} (h : ∀ x, P x ↔ Q x) : (∃ x, P x) ↔ (∃ x, Q x) := by
  constructor 
  · intros h' 
    obtain ⟨x,hpx⟩ := h' 
    have hx : P x ↔ Q x := h x 
    obtain ⟨hpq,hqp⟩ := hx 
    use x 
    apply hpq hpx 
  · intros h' 
    obtain ⟨x,hqx⟩ := h' 
    have hx : P x ↔ Q x := h x 
    obtain ⟨hpq,hqp⟩ := hx 
    use x 
    apply hqp hqx
