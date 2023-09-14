example {x : ℤ} (h1 : x + 4 = 2) : x = -2 :=
begin
  have h2 : x = 2 - 4,
  { exact eq.subst h1 (eq.refl (x + 4 - 4)) },
  exact h2
end