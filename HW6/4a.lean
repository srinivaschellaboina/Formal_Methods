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

example {P Q : α → Prop} (h : ∀ x, P x ↔ Q x) : (∃ x, P x) ↔ (∃ x, Q x) := by
  constructor
  . intro temp
    obtain ⟨x,temp⟩ := temp;have temp2: P x ↔ Q x := by apply h x
    obtain ⟨temp3,temp4⟩ := temp2;have temp3: Q x := by apply temp3 temp
    use x; apply temp3
  . intro temp
    obtain ⟨x,temp⟩ := temp
    have temp2: P x ↔ Q x := by apply h x
    obtain ⟨temp3,temp4⟩ := temp2
    have temp3: P x := by apply temp4 temp
    use x
    apply temp3
/-Please leave a blank line below this to avoid errors--/
