-- De Morgan's Law 2: ¬(p ∨ q) → (¬p ∧ ¬q)
lemma de_morgan_2 {p q : Prop} : ¬(p ∨ q) → (¬p ∧ ¬q) :=
λ h, ⟨λ hp, h (or.inl hp), λ hq, h (or.inr hq)⟩
