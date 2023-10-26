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
  push_neg
  constructor
  . intro h
    apply h
  . intro h
    apply h
