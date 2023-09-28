import Mathlib.Data.Real.Basic
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use

--- Problem 4

-- Example 2.5.2
example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by
  obtain ⟨x, hxt⟩ := h
  have H := le_or_gt x 0
  obtain hx | hx := H
  · have hxt' : 0 < (-x) * t := by addarith [hxt]
    have hx' : 0 ≤ -x := by addarith [hx]
    cancel -x at hxt'
    apply ne_of_gt
    apply hxt'
  · have hxt' : 0 > x * (-t) := by extra [hxt]

-- Example 2.5.6
example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use a + 1 
  use a
  calc
    (a + 1)^2 - a^2 = a^2 + a + a + 1 - a^2 := by ring
    _ = 2 * a + 1 := by ring
 
-- Example 2.5.7
example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p + q) / 2
  have hgreater: p < (p+q)/2  := 
    calc
      p = (p + p)/2 := by ring
      _ < (p+q)/2 := by rel [h]

  have hless: (p+q)/2 < q :=
    calc
      (p+q)/2 < (q+q)/2 := by rel [h]
      _ = q := by ring
  apply And.intro hgreater hless
  
-- Problem 5

--- Problem 2.5.9 (Exercise 5)
example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  use x + 1/2
  have h1 := 
  calc
    (x + 1/2)^2 = x^2 + x + 1/4 := by ring
    _ = (x^2 + 1/4) + x := by ring
    _ ≥ (0 + 1/4) + x  := by extra
    _ > x := by extra 
  apply h1

--- Problem 2.5.9 (Exercise 6)
example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  obtain ⟨a, h2 ⟩ := h
  have h2 := le_or_gt a 0
  obtain ha | ha := h2
  have ha' : t < 1 :=
  --calc
   -- a*t - t + 1 < a := by addarith [h2]
    --t*(a-1) + 1 = _ := by ring
    --_ = t*(a-1) + 1  := by ring

    --t * (a - 1) + 1 < a := by addarith 
    --t * (a - 1) < a - 1 := by ring
    --t < (a-1)/(a-1) := by ring
    --_ < 1 := by ring 

example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  obtain ⟨a, h1⟩ := h
  have h2 := le_or_succ_le a 2
  obtain ha | ha := h2
  have h3: m ≤ 4 := 
  calc
    m ≤ 2 * 2 := by rel [ha] 
    --_ ≤ 4 := by numbers


