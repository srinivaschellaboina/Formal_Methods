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

theorem problem4b (P : α → β → Prop) : (∃ x y, P x y) ↔ ∃ y x, P x y := by
  constructor 
  · intros h 
    obtain ⟨x,y,hxy⟩ := h 
    use y 
    use x 
    apply hxy 
  · intros h 
    obtain ⟨y,x,hyx⟩ := h 
    use x 
    use y 
    apply hyx
