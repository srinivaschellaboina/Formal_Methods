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


example (a b c : ℤ) : Even (a - b) ∨ Even (a + c) ∨ Even (b - c) :=
by_cases (Even a)
  (intro ha; right; apply Even.add_left ha; exact c)
  (intro ha;
    by_cases (Even b)
      (intro hb; left; apply Even.sub_left hb; exact a)
      (intro hb;
        by_cases (Even c)
          (intro hc; right; left; apply Even.add_right hc; exact a)
          (intro hc; left; exact Even.sub_odd_odd ha hb)
      )
  )




