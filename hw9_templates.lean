
import Mathlib.Data.Real.Basic
import Library.Theory.Parity
import Library.Theory.Comparison
import Library.Theory.Prime
import Library.Tactic.Induction
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Use
import Mathlib.Tactic.GCongr
import Library.Tactic.Cancel

notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r

def B : ℕ → ℚ
  | 0 => 0
  | n + 1 => B n + (n + 1 : ℚ) ^ 2

/- 2 points -/
theorem problem4a (n : ℕ) : B n = n * (n + 1) * (2 * n + 1) / 6 := by
  simple_induction n with k FM
  . simp [B]
  . simp [B, FM]; ring


def S : ℕ → ℚ
  | 0 => 1
  | n + 1 => S n + 1 / 2 ^ (n + 1)

/- 3 points -/
theorem problem4b (n : ℕ) : S n = 2 - 1 / 2 ^ n := by
  simple_induction n with k FM
  . simp [S]; numbers
  . simp [S, FM]; ring


/- 3 points -/
theorem problem4c (n : ℕ) : S n ≤ 2 := by
  simple_induction n with k FM
  . simp [S]
  . have FM: S (k+1) = 2 - 1 / 2 ^ (k+1);
    apply problem4b; simp [FM]



def factorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

notation:10000 n "!" => factorial n

/- 3 points -/
theorem problem4d (n : ℕ) : (n + 1) ! ≤ (n + 1) ^ n := by
  simple_induction n with bc inductive_step
  . simp [factorial]
  . have prev : ℕ := bc
    have pow_inequality : (bc + 1) ^ prev ≤ (bc + 2) ^ prev := by
      simple_induction prev with index index_hypothesis
      . simp
      . calc
          (bc + 1) ^ (index + 1) = (bc + 1) ^ index * (bc + 1) := by ring
          _ ≤ (bc + 1) ^ index * (bc + 2) := by simp
          _ ≤ (bc + 2) ^ index * (bc + 2) := by rel[index_hypothesis]
          _ = (bc + 2) ^ (index + 1) := by ring
    have bc_inequality: bc ≤ bc + 1 := by extra
    calc
      (bc + 2)! = (bc + 2) * (bc + 1)! := by rw [factorial]
      _ ≤ (bc + 2) * (bc + 1) ^ bc := by rel[inductive_step]
      _ ≤ (bc + 2) * (bc + 2) ^ bc := by rel[pow_inequality, bc_inequality]
      _ = (bc + 2) ^ (bc + 1) := by ring

def q : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | n + 2 => 2 * q (n + 1) - q n + 6 * n + 6

/- 3 points -/
theorem problem5a (n : ℕ) : q n = (n:ℤ) ^ 3 + 1 := by
  two_step_induction n with k IH1 IH2
  . simp
  . simp
  . calc
      q (k + 1 + 1) = 2 * ((k + 1 :ℤ ) ^ 3 + 1) - ((k:ℤ ) ^ 3 + 1) + 6*k + 6 := by rw [q, IH1, IH2]
      _ = (↑k + 1 + 1) ^ 3 + 1 := by ring


def r : ℕ → ℤ
  | 0 => 2
  | 1 => 0
  | n + 2 => 2 * r (n + 1) + r n

/- 3 points -/
theorem problem5b : forall_sufficiently_large n : ℕ, r n ≥ 2 ^ n := by
  use 7
  intro n FM
  two_step_induction_from_starting_point n, FM with k hk IH1 IH2
  . simp
  . simp
  . calc
      r (k + 1 + 1) ≥ 2 * (2 ^ (k + 1)) + 2 ^ k := by rw[r]; rel[IH2, IH1]
      _ = 2 ^ (k + 2) + 2 ^ k := by ring
      _ ≥ 2 ^ (k + 2) := by extra



/- 3 points -/
theorem problem5c (n : ℕ) (hn : 0 < n) : ∃ a x, Odd x ∧ n = 2 ^ a * x := by
  obtain hn | hn := Nat.even_or_odd n
  . obtain ⟨c,fm⟩ := hn
    rw [fm] at hn
    cancel 2 at hn
    have fi : ∃ a x, Odd x ∧ c = 2 ^ a * x := problem5c c hn
    obtain ⟨a', y', hy', fm2⟩ := fi
    use a'+1, y'
    use hy'
    calc
      n = 2 * (2^a' * y') := by rw [fm, fm2]
      _ = 2^(a'+1)*y' := by ring
  . use 0, n
    simp
    apply hn
