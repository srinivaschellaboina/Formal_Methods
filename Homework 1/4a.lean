example {a b : ℤ} (h1 : a = 2 * b + 5) (h2 : b = 3) : a = 11 :=
begin
  rw h2 at h1,  
  rw h1,       
  exact rfl,   
end