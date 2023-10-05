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

--- Problem 4

-- MoP Example 3.1.4
example {n : ℤ} (hn : Odd n) : Odd (7 * n - 4) := by
  dsimp [Odd] at *
  obtain ⟨k, hk⟩ := hn
  use 7 * k + 1
  calc
    7 * n - 4 = 7 * (2 * k + 1) - 4 := by rw [hk]
    _ = 14 * k + 7 - 4 := by ring
    _ = 2 * (7 * k + 1) + 1 := by ring
  
-- MoP Example 3.1.6
example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y + 2 * y) := by
  dsimp [Odd] at *
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  use 2*a*b + 3*b + a + 1
  calc
    x * y + 2 * y = (2*a + 1) * (2*b + 1) + 2*(2*b + 1) := by rw [ha, hb]
    _ = 2*(2*a*b + 3*b + a + 1) + 1 := by ring

-- MoP Example 3.1.8
example {n : ℤ} (hn : Even n) : Odd (n^2 + 2*n - 5) := by
  dsimp [Odd] at *
  obtain ⟨a, ha⟩ := hn
  use 2*a^2 + 2*a - 3
  calc
    n^2 + 2*n - 5 = (a+a)^2 + 2*(a+a) - 5 := by rw [ha]
    _ = 2*(2*a^2 + 2*a - 3) + 1 := by ring

-- MoP Exercise 14  3.1.10 Exercises
example (a b c : ℤ) : Even (a - b) ∨ Even (a + c) ∨ Even (b - c) := by
  sorry
--- Problem 5

-- MoP Example 4.1.3
example {a b : ℝ} (h : ∀ x, x ≥ a ∨ x ≤ b) : a ≤ b := by
  have h1 : (a+b)/2 ≥ a ∨ (a+b)/2 ≤ b := by apply h
  cases h1 with 
    | inl ha => 
      calc
        b = 2 * ((a+b)/2) - a := by ring
        _ ≥ 2*a - a := by rel [ha] 
        _ = a := by ring
    | inr hb =>
      calc
        a = 2 * ((a+b)/2) - b := by ring
        _ ≤ 2*b - b := by rel [hb]
        _ = b := by ring

--- If you have ∀ statment, then you can use
-- have Pn : P(n) := h

--- eq_zero_or_eq_zero_of_mul_eq_zero
-- h: (x-a)(x-b) = 0
-- (x-a)=0 ∨ (x-b)=0

--- le_antisymm
-- if a ≤ b ∨ b ≤ a
-- then a = b

-- MoP Example 4.1.6
example : ∃ c : ℝ, ∀ x y, x ^ 2 + y ^ 2 ≤ 4 → x + y ≥ c := by
  -- you are advised to use abs_le_of_sq_le_sq'
  sorry

-- MoP Exercise 2 Subsection 4.1.10
example {n : ℤ} (hn : ∀ m, 1 ≤ m → m ≤ 5 → m ∣ n) : 15 ∣ n := by
  sorry

--- Problem 6

-- MoP Example 4.2.5
example {x : ℝ} : x^2  + x - 6 = 0 ↔ x = -3 ∨ x = 2 := by
  constructor 
  . intro h1
    have H : (x + 3) * (x - 2) = 0 :=
    calc
      (x + 3) * (x - 2) = x^2 + x - 6 := by ring
      _ = 0 := by rw [h1]
    have H' : x + 3 = 0 ∨ x -2 = 0 := by apply eq_zero_or_eq_zero_of_mul_eq_zero H
    obtain h2 | h3 := H'
    sorry
  . intro HH




  
