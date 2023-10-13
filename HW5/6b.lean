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

example {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h_pyth : a ^ 2 + b ^ 2 = c ^ 2) : 3 ≤ a := by
      have ha1 : a ≤ 2 ∨ a ≥ 3 := by apply le_or_succ_le a 2 
      obtain ha2|ha3 := ha1
      . have hb1 : b ≤ 1 ∨ b ≥ 2 := by apply le_or_succ_le b 1
        obtain hb2|hb3 := hb1
        . have hc1 : c^2 < 3^2:= by
            calc 
              c^2 = a^2 + b^2 := by rw[h_pyth]
              _ ≤ 2^2 + b^2  := by rel[ha2]
              _ ≤ 2^2 + 1 ^ 2 := by rel[hb2]
              _ <  3^2 := by numbers
          have hc2: c < 3 := by 
            obtain hc3|hc4 := lt_or_ge c 3
            . apply hc3
            . have hc5: c^2 ≥  3^2 := by
                calc
                  c^2 = c*c := by ring
                  _ ≥ 3 *3 := by rel[hc4]
              have hc6: ¬ c^2 < 3^2 := by
                apply not_lt_of_ge
                addarith[hc5]
              contradiction
          have ha3: a < 2 ∨ a = 2 := by apply Nat.lt_or_eq_of_le ha2 
          obtain ha4|hha5 := ha3
          . have ha4: a ≤ 1 := by addarith[ha4]
            have ha3: a < 1 ∨ a = 1 := by apply Nat.lt_or_eq_of_le ha4
            obtain ha5|ha6 := ha3 
            . have ha7 : a ≤ 0 := by addarith[ha5]
              have ha8: ¬ a ≤  0 := by
                apply not_le_of_gt
                extra
              contradiction
            have hb3: b < 1 ∨ b = 1 := by apply Nat.lt_or_eq_of_le hb2
            obtain hb4|hb5 := hb3
            . have hb6: b ≤ 0:= by addarith[hb4]
              have hb7: ¬ b ≤ 0 := by
                apply not_le_of_gt
                extra
              contradiction
            . have hc3: c ≤ 2 := by addarith[hc2]
              have hc3: c < 2 ∨ c = 2 := by apply Nat.lt_or_eq_of_le hc3
              obtain hc4|hc5 := hc3
              . have hc5: c ≤ 1 := by addarith[hc4]
                have hc6: c < 1 ∨ c = 1 := by apply Nat.lt_or_eq_of_le hc5
                obtain hc7|hc8 := hc6
                . have hc9: c ≤ 0 := by addarith[hc7]
                  have hc10 : ¬ c ≤ 0:= by
                    apply not_le_of_gt
                    extra
                  contradiction
                . have cc: 2 = 1 := by
                    calc 
                      2 = 1 + 1 := by numbers
                      _ = 1^2 + 1^2 := by numbers
                      _ = a^2 + b^2 := by rw[ha6,hb5]
                      _ = c^2 := by rw [h_pyth]
                      _ = 1^2 := by rw[hc8]
                      _ = 1 := by numbers
                  contradiction
              . have cc: 2 = 4 := by
                  calc
                    2 = 1 + 1 := by numbers
                      _ = 1^2 + 1^2 := by numbers
                      _ = a^2 + b^2 := by rw[ha6,hb5]
                      _ = c^2 := by rw [h_pyth]
                      _ = 2^2 := by rw[hc5]
                      _ = 4 := by numbers
                contradiction
          . have hb3: b < 1 ∨ b = 1 := by apply Nat.lt_or_eq_of_le hb2
            obtain hb4|hb5 := hb3
            . have hb6: b ≤ 0:= by addarith[hb4]
              have hb7: ¬ b ≤ 0 := by
                apply not_le_of_gt
                extra
              contradiction
            . have hc3: c ≤ 2 := by addarith[hc2]
              have hc3: c < 2 ∨ c = 2 := by apply Nat.lt_or_eq_of_le hc3
              obtain hc4|hc5 := hc3
              . have hc5: c ≤ 1 := by addarith[hc4]
                have hc6: c < 1 ∨ c = 1 := by apply Nat.lt_or_eq_of_le hc5
                obtain hc7|hc8 := hc6
                . have hc9: c ≤ 0 := by addarith[hc7]
                  have hc10 : ¬ c ≤ 0:= by
                    apply not_le_of_gt
                    extra
                  contradiction
                . have cc: 5 = 1 := by
                    calc 
                      5 = 4 + 1 := by numbers
                      _ = 2^2 + 1^2 := by numbers
                      _ = a^2 + b^2 := by rw[hha5,hb5]
                      _ = c^2 := by rw [h_pyth]
                      _ = 1^2 := by rw[hc8]
                      _ = 1 := by numbers
                  contradiction
              . have cc: 5 = 4 := by
                  calc
                    5 = 4 + 1 := by numbers
                      _ = 2^2 + 1^2 := by numbers
                      _ = a^2 + b^2 := by rw[hha5,hb5]
                      _ = c^2 := by rw [h_pyth]
                      _ = 2^2 := by rw[hc5]
                      _ = 4 := by numbers
                contradiction
        . have hb4: b^2 < c^2 := by
            calc
              b^2 < a^2 + b^2  := by extra
              _ = c^2 := by rw [h_pyth]   
          have hb5:b < c := by 
            have hb6:= lt_or_ge b c 
            obtain hb6|hb7 := hb6
            . apply hb6
            . have hb8 : b^2 ≥ c^2 := by 
                calc 
                  b^2 = b^2 := by ring
                  _ ≥ c^2 := by rel[hb7]
              have hc10 : ¬ b^2 < c^2:= by
                    apply not_lt_of_ge
                    addarith[hb8]
              contradiction              
          have hb5: b + 1 ≤ c := by addarith[hb5]
          have hb6: c^2 < (b+1)^2 := by
            calc 
              c^2 = a^2 + b^ 2 := by rw[h_pyth]
              _ ≤ 2^2 + b^2 := by rel[ha2]
              _ = b^2 + 2*2 := by ring
              _ ≤ b^2 + 2*b := by rel[hb3]
              _ < b^2 + 2*b + 1 := by extra
              _ = (b+1)^2 := by ring
          have hb7: c < b+1 := by 
            have hb6:= lt_or_ge c (b+1) 
            obtain hb8|hb9 := hb6
            . apply hb8
            . have hb9 : c^2 ≥ (b+1)^2  := by 
                calc 
                  c^2 = c^2 := by ring
                  _ ≥ (b+1)^2 := by rel[hb9]
              have hc10 : ¬ c ^ 2 < (b + 1) ^ 2:= by
                  apply not_lt_of_ge
                  addarith[hb9]
              contradiction
          have hb8: ¬ c < b+1 := by
            apply not_lt_of_ge
            addarith[hb5]
          contradiction              
      . addarith[ha3]