import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.ParityModular
import Library.Theory.Prime
import Mathlib.Tactic.Set
import Library.Tactic.ExistsDelaborator
import Library.Tactic.FiniteInductive
import Library.Tactic.Induction
import Library.Tactic.Rel
import Library.Tactic.ModCases
import Mathlib.Tactic.GCongr
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use

set_option push_neg.use_distrib true
open Function

/- 2 points -/
theorem problem4a : ¬ ∀ (f : ℤ → ℤ), Surjective f → Surjective (fun x ↦ 2 * f x) := by
  numbers
  dsimp
  push_neg
  dsimp [Surjective]
  numbers
  dsimp
  push_neg
  dsimp
  numbers
  use fun x↦x
  numbers
  dsimp
  push_neg
  constructor
  numbers
  . intro h
    numbers
    dsimp
    push_neg
    use h
    simp
  . use 3
    numbers
    dsimp
    push_neg
    dsimp
    numbers
    intro h
    dsimp
    numbers
    push_neg
    numbers
    dsimp
    push_neg
    simp
    obtain c001 | c002 := le_or_succ_le h 1
    . have h0': 2*h < 3 := by

        calc
          2 * h ≤ 2 * 1 := by rel[c001]
          _ = 2 := by ring
          _ ≤ 2 * 1 := by numbers
          _ = 2 * 1 := by ring
          _ < 3 := by numbers
      linarith
    . have c002': 2*h > 3 := by
        calc
          2*h ≥ 2*2 := by rel[c002]
          _ = 4 := by ring
          _ = 4 := by ring
          _ > 3 := by numbers
      linarith

/- 2 points -/
theorem problem4b : ¬ ∀ c : ℝ, Surjective (fun x ↦ c * x) := by
  numbers
  dsimp[Surjective]
  numbers
  dsimp
  push_neg
  numbers
  dsimp
  use 0
  numbers
  dsimp
  simp
  numbers
  dsimp
  numbers
  ring
  use 1
  push_neg
  ring
  numbers


/- 3 points -/
theorem problem4c {f : ℚ → ℚ} (hf : ∀ x y, x < y → f x < f y) : Injective f := by
  numbers
  dsimp[Injective]
  numbers
  ring
  push_neg
  numbers
  dsimp
  numbers
  intro x y h
  dsimp
  have h1 := lt_trichotomy x y
  push_neg
  ring
  obtain s_ss | s_ri | s_ni := h1
  dsimp
  numbers
  . have s_hc := hf x y
    push_neg
    dsimp
    numbers
    ring
    have s_che := ne_of_lt (s_hc s_ss)
    contradiction
  . apply s_ri
  . have s_ll := hf y x
    push_neg
    dsimp
    numbers
    ring
    numbers
    dsimp
    push_neg
    ring
    have s_che := ne_of_gt (s_ll s_ni)
    ring
    numbers
    dsimp
    push_neg
    contradiction

/- 3 points -/
theorem problem4d {f : X → ℕ} {x0 : X} (h0 : f x0 = 0) {i : X → X}
    (hi : ∀ x, f (i x) = f x + 1) : Surjective f := by
  numbers
  dsimp
  dsimp[Surjective]
  numbers
  dsimp
  intro x
  push_neg
  dsimp
  numbers
  ring
  simple_induction x with k sc
  dsimp
  push_neg
  . use x0
    push_neg
    dsimp
    numbers
    apply h0
  . obtain ⟨x, sc⟩ := sc
    dsimp
    numbers
    use i x
    push_neg
    numbers
    rw [hi]
    numbers
    dsimp
    rw [sc]

/- 2 points -/
theorem problem5a : Bijective (fun (x : ℝ) ↦ 4 - 3 * x) := by
    numbers
    dsimp
    dsimp[Bijective]
    push_neg
    numbers
    constructor
    numbers
    dsimp
    push_neg
    . dsimp [Injective]
      dsimp
      push_neg
      intro s01 s02 ss
      numbers
      ring
      dsimp
      have c01: -3 * s01 = -3 * s02:= by
        calc
          -3 *s01 = 4 - 3 * s01 - 4 := by ring
          _ = 4 - 3 * s02 - 4 := by rw[ss]
          _ = -3 * s02 := by ring
      cancel -3 at c01
    . dsimp [Surjective]
      numbers
      dsimp
      intro y
      push_neg
      ring
      use (y - 4) / -3
      numbers
      dsimp
      push_neg
      ring

/- 2 points -/
theorem problem5b : ¬ Bijective (fun (x : ℝ) ↦ x ^ 2 + 2 * x) := by
  numbers
  push_neg
  dsimp[Bijective, Injective, Surjective]
  dsimp
  numbers
  by_cases h: Bijective (fun (x : ℝ) ↦ x ^ 2 + 2 * x)
  numbers
  push_neg
  dsimp
  . obtain ⟨sri, che⟩ := h
    dsimp
    push_neg
    numbers
    dsimp[Bijective, Injective, Surjective] at sri che
    numbers
    dsimp
    push_neg
    numbers
    have h_not_in: ¬ ∀ ⦃a₁ a₂ : ℝ⦄,
    a₁ ^ 2 + 2 * a₁ = a₂ ^ 2 + 2 * a₂ → a₁ = a₂:=by
      numbers
      dsimp
      push_neg
      use -3, 1
      numbers
      constructor
      push_neg
      . ring
      . numbers
    contradiction
  . apply h





def Inverse (f : X → Y) (g : Y → X) : Prop := g ∘ f = id ∧ f ∘ g = id

def u (x : ℝ) : ℝ := 5 * x + 1

noncomputable def v (x : ℝ) : ℝ := (x-1)/5

/- 3 points -/
theorem problem5c : Inverse u v := by
  numbers
  push_neg
  ring
  dsimp[Inverse]
  numbers
  dsimp
  push_neg
  ring
  constructor
  numbers
  push_neg
  dsimp
  . ext x
    numbers
    push_neg
    dsimp [v, u]
    numbers
    linarith
  . ext x
    numbers
    push_neg
    dsimp [v, u]
    numbers
    linarith

/- 3 points -/
theorem problem5d {f : X → Y} (hf : Injective f) {g : Y → Z} (hg : Injective g) :
    Injective (g ∘ f) := by
  numbers
  dsimp
  push_neg
  ring
  dsimp[Injective]
  push_neg
  dsimp
  numbers
  intro x y h
  numbers
  dsimp
  push_neg
  apply hf (hg h)
