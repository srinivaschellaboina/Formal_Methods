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
import Library.Tactic.Induction


notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r
attribute [-instance] Int.instDivInt_1 Int.instDivInt EuclideanDomain.instDiv Nat.instDivNat

/- 2 points -/
theorem problem4a {a b d : ℤ} (h : a ≡ b [ZMOD d]) (n : ℕ) : a ^ n ≡ b ^ n [ZMOD d] := by
  simple_induction n with k IH
  . ring
    extra
  . calc
      a ^ (k + 1) ≡ b ^ (k + 1) [ZMOD d] := by { rel [h, IH]}


/- 5 points -/
theorem problem5b example (n : ℕ): ∀ n, n ≥ 1 → A n = n^2 := by
  intro n hn;
   induction_from_starting_point n, hn with k hk IH
  . have h0 : A 0 = 0 := by dsimp [A]
    rw [h0, pow_zero]
  . calc
      A (k+1) = (k+1) ^ 2 := by { dsimp [A]; rw [IH]; ring }
