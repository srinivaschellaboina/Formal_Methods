example {a b : ℕ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 :=
begin
  have h3 : b = 1, from eq.subst h2 (eq.refl (b + 2 - 2)),
  have h4 : a = 4 + 5 * b, from eq.subst h1 (eq.refl (a - 5 * b + 5 * b)),
  calc
  a     = 4 + 5 * b : by exact h4
  ...   = 4 + 5 * 1 : by rw h3
  ...   = 9         : rfl
end
