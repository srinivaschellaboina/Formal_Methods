example (P Q R : Prop) (h : P → (Q → R)) : (P → Q) → (P → R) :=
begin
  intro hPQ,
  intro hP,
  have hQ := hPQ hP,
  have hQR := h hP,
  exact hQR hQ,
end
