import Mathlib.Data.Nat.Basic
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

-- MoP Subsection 4.2.10 Exercise 2
 example {n : ℤ} : 63 ∣ n ↔ 7 ∣ n ∧ 9 ∣ n := by
  constructor
  . intro h_63
    obtain ⟨k, hk⟩ := h_63
    constructor
    . dsimp [(· ∣ ·)]
      use 9 * k
      calc
        n = 63 * k := by rel [hk]
        _ = 7 * (9 * k) := by ring
    . dsimp [(· ∣ ·)]
      use 7 * k
      calc
        n = 63 * k := by rel [hk]
        _ = 9 * (7 * k) := by ring
  . intro h_7_and_9
    obtain ⟨h7, h9⟩ := h_7_and_9
    obtain ⟨a, ha⟩ := h7
    obtain ⟨b, hb⟩ := h9
    dsimp [(· ∣ ·)]
      



-- MoP Subsection 4.2.10 Exercise 5
example {k : ℕ} : k ^ 2 ≤ 6 ↔ k = 0 ∨ k = 1 ∨ k = 2 := by
  constructor
  . intro h
    have k_less_3 : k^2 < 3^2 :=
    calc
     k^2 ≤ 6 := h
     _ < 3^2 := by numbers
    cancel 2 at k_less_3
    interval_cases k
    . left
      numbers
    . right
      . left
        numbers
    . right
      . right
        numbers
  . intro hk
    cases hk with
      | inl hk0 =>
        calc
          k^2 = 0^2 := by rw [hk0]
          _ ≤ 6 := by numbers
      | inr hk_1_or_2 =>
        cases hk_1_or_2 with
          | inl hk1 =>
            calc
              k^2 = 1^2 := by rw [hk1]
              _ ≤ 6 := by numbers
          | inr hk2 =>
            calc
              k^2 = 2^2 := by rw [hk2]
              _ ≤ 6 := by numbers

--- Problem 5

-- MoP Section 4.3 Example 4.3.2
example : ∃! x : ℚ, ∀ a, a ≥ 1 → a ≤ 3 → (a - x) ^ 2 ≤ 1 := by
  use 2
  dsimp
  constructor
  . intros a ha1 ha3
    have ha1'' : a - 2 ≤ 1 := by
      calc
        a - 2 ≤ 3 - 2 := by rel [ha3]
        _ ≤ 1 := by ring
    have ha1' : a - 2 ≥ -1 := by
      calc
        a - 2 ≥ 1 - 2 := by rel [ha1]
        _ ≥ -1 := by ring
    have ha_sq : (a-2)^2 ≤ 1^2 := by
      apply sq_le_sq'
      apply ha1'
      apply ha1''
    calc
      (a-2)^2 ≤ 1^2 := ha_sq
      _ = 1 := by numbers
  . intros y ha
    have hay1 := ha 1
    have  h' : (1 - y)^2 ≤ 1 := by 
      apply hay1
      simp
      simp
    --have hay1 : (1 - y)^2 ≤ 1 := ha 1
    have hay3 : (3 - y)^2 ≤ 1 := by apply ha
    have hy2 : (y - 2)^2 ≤ 0^2 := by
      calc
        (y - 2)^2 = ((1-y)^2 + (3 - y)^2 - 2)/2 := by ring
        _ ≤ (1 + 1 - 2) / 2 := by rel [hay1, hay3]
        _ = 0^2 := by numbers
    cancel 2 at hy2
    have hy2' : y ≤ 2 := by
      calc
        y = y - 2 + 2 := by ring
        _ ≤ 0 + 2 := by rel [hy2]
        _ ≤ 2 := by ring
    have hy2pos : (y - 2)^2 ≥ 0^2 := by numbers
    cancel 2 at hy2pos
    have hy2'' : y ≥ 2 := by
      calc
        y = y - 2 + 2 := by ring
        _ ≥ 0 + 2 := by rel [hy2pos]
        _ ≥ 2 := by ring
    apply le_antisymm
    extra
    extra

-- MoP Section 4.3 Exercise 1
example : ∃! x : ℚ, 4 * x - 3 = 9 := by
  use 3
  dsimp
  constructor
  numbers
  . intro y
    intro hy
    calc
      y = (4 * y - 3) / 4 + 3/4 := by ring
      _ = 9/4 + 3/4  := by rw [hy]
      _ = 3 := by ring

-- MoP Section 4.3 Exercise 2
example : ∃! n : ℕ, ∀ a, n ≤ a := by
  use 0
  dsimp
  constructor
  extra
  . intro n
    intro ha
    have h_n_geq_0 : 0 ≤ n := by extra 
    have h_n_leq_0 : n ≤ 0 := by apply ha
    apply le_antisymm 
    extra
    extra

--- Problem 6

-- MoP Section 4.4 Example 4.4.4
example {p : ℕ} (hp : 2 ≤ p) (H : ∀ m : ℕ, 1 < m → m < p → ¬m ∣ p) : Prime p := by
  constructor
  · apply hp -- show that `2 ≤ p`
  intro m hmp
  have hp' : 0 < p := by extra
  have h1m : 1 ≤ m := Nat.pos_of_dvd_of_pos hmp hp'
  obtain hm | hm_left : 1 = m ∨ 1 < m := eq_or_lt_of_le h1m
  · -- the case `m = 1`
    left
    addarith [hm]
  -- the case `1 < m`
  sorry

-- MoP Section 4.4 Example 4.4.5
example {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h_pyth : a ^ 2 + b ^ 2 = c ^ 2) : 3 ≤ a := by
      obtain ⟨ha2, ha3⟩ := le_or_succ_le a 3
      numbers
      sorry

-- MoP Section 4.4 Example 4.4.6 Exercise 1
example {x y : ℝ} (n : ℕ) (hx : 0 ≤ x) (hn : 0 < n) (h : y ^ n ≤ x ^ n) :
    y ≤ x := by
  sorry

namespace Nat
-- MoP Section 4.4 Example 4.4.6 Exercise 5
example (p : ℕ) (h : Prime p) : p = 2 ∨ Odd p := by
  have de_morgan : ¬(p = 2) ∧ ¬(Odd p)
  obtain hp1 | hp2 := de_morgan
  sorry

