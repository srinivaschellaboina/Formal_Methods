example (P Q R : Prop) (h : P ∧ (Q → R)) : P → (Q → R) :=
begin
  intro hP,
  have hQR : Q → R := h.right,
  intro hQ,
  exact hQR hQ,
end