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

theorem problem4c (P : α → β → Prop) : (∀ x y, P x y) ↔ ∀ y x, P x y := by
  constructor <;> intros h y x <;> apply h x y
