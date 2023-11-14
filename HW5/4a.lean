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

example {n : ℤ} : 63 ∣ n ↔ 7 ∣ n ∧ 9 ∣ n := by
  constructor 
  · intros h 
    dsimp [(.∣.)] at * 
    obtain ⟨c,hc⟩ := h 
    constructor 
    · use 9 * c 
      calc 
        n = 63 * c := by rw [hc] 
        _ = 7 * (9 * c) := by ring 
    · use 7 * c 
      calc 
        n = 63 * c := by rw [hc] 
        _ = 9 * (7 * c) := by ring 
  · intros h 
    dsimp [(.∣.)] at * 
    obtain ⟨h1,h2⟩ := h 
    obtain ⟨a,ha⟩ := h1 
    obtain ⟨b,hb⟩ := h2 
    use 4 * b - 3 * a 
    calc 
      n = 28 * n - 27 * n := by ring 
      _ = 4 * 7 * n + (-3) * 9 * n := by ring 
      _ = 4 * 7 * (n) + (-3) * 9 * (7 * a) := by rw [ha] 
      _ = 4 * 7 * (9 * b) + (-3) * 9 * (7 * a) := by rw [hb] 
      _ = 63 * (4 * b - 3 * a) := by ring 
