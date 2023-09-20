import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel

-- Problem 5c
theorem deMorgan2 {p q : Prop} : (¬p ∧ ¬q) → ¬(p ∨ q) := by
  intro h1
  obtain ⟨notp, notq⟩ := h1
  intro h2
  cases h2 with
    | inl hp => exact notp hp
    | inr hq => exact notq hq

-- Problem 5d
theorem deMorgan3 {p q : Prop} : (¬p ∨ ¬q) → ¬(p ∧ q) := by
  intro h1
  intros p_and_q
  obtain ⟨hp, hq⟩ := p_and_q
  cases h1 with
    | inl notp => exact notp hp 
    | inr notq => exact notq hq

-- Problem 6a
example {x y : ℤ} (h1 : x + 3 ≥ 2 * y) (h2 : 1 ≤ y) : x ≥ -1 :=
  calc
    x = (x + 3) - 3 := by ring
    _ ≥ 2 * y - 3 := by rel [h1]
    _ ≥ 2 * 1 - 3 := by rel [h2]
    _ ≥ -1 := by numbers

-- Problem 6b
example {a b : ℚ} (h1 : 3 ≤ a) (h2 : a + 2 * b ≥ 4) : a + b ≥ 3 := 
  calc
    (a + b) = (a + (a + 2 * b)) / 2 := by ring
    _ ≥ (a + 4) / 2:= by rel [h2]
    _ ≥ (3 + 4) / 2 := by rel [h1]
    _ ≥ 3 := by numbers

-- Problem 6c
example {x : ℤ} (hx : x ≥ 9) : x ^ 3 - 8 * x ^ 2 + 2 * x ≥ 3 := 
  calc
    x ^ 3 - 8 * x ^ 2 + 2 * x = x * (x^2 - 8*x + 2) := by ring
    _ = x * x * (x - 8) + 2 * x := by ring
    _ ≥ x * x * (9 - 8) + 2 * x := by rel [hx]
    _ ≥ 9 * 9 * (9 - 8) + 2 * 9 := by rel [hx]
    _ ≥ 3 := by numbers

