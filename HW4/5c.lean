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

example {n : ℤ} (hn : ∀ m, 1 ≤ m → m ≤ 5 → m ∣ n) : 15 ∣ n := 
  have h3 : 3 ∣ n := hn 3 (by ring) (by ring);
  have h5 : 5 ∣ n := hn 5 (by ring) (by ring);
  have h15 : 15 = 3 * 5 := by ring;





