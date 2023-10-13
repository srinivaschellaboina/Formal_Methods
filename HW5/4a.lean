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
  . intro hn
    obtain ⟨k,hk⟩ := hn
    constructor
    . use (9*k)
      calc 
        n = 63 * k := by rw[hk]
        _ = 7 * (9 * k) := by ring
    . use (7*k)
      calc 
        n = 63 * k := by rw[hk]
        _ = 9 *(7*k) := by ring
  . intro hn
    obtain ⟨hk,hq⟩ := hn
    obtain ⟨k,h7⟩ := hk
    have hqq : 9 ∣ 7*k := by 
      calc
          9 ∣ n  := by exact hq
          _  ∣ 7*k := by rw [h7]

    obtain ⟨q,hkq⟩ := hqq 
    have h1 : 9 ∣ k := by
      use (4*q - 3* k)
      calc
        k = 28 * k - 27 * k := by ring
        _ = 4* (7 * k) - 27 * k  := by ring
        _ = 4 * (9 * q) - 27 * k := by rw[hkq]
        _ = 9 * (4 * q - 3 * k) := by ring
    obtain ⟨x,h2⟩ := h1
    use x
    calc
      n = 7 * k := by exact h7
      _ = 7 * (9 * x) := by rw[h2]
      _ = 63 * x := by ring