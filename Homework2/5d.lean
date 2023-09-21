-- De Morgan's Law 3: ¬(p ∧ q) → (¬p ∨ ¬q)
lemma de_morgan_3 {p q : Prop} : ¬(p ∧ q) → (¬p ∨ ¬q) :=
λ h, if hp : p then or.inr (λ hq, h ⟨hp, hq⟩) else or.inl hp
