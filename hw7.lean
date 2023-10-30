import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.Prime
import Library.Tactic.Rel
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use


--- Problem 4

-- MoP Section 5.3 Example 5.3.5
example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  push_neg
  intro n
  have hn := le_or_succ_le n 1
  obtain hn | hn := hn
  · apply ne_of_lt
    calc
      n ^ 2 ≤ 1 ^ 2 := by rel [hn]
      _ < 2 := by numbers
  · apply ne_of_gt
    calc
      n^2 ≥ 2^2 := by rel [hn]
      _ ≥ 4 := by numbers
      _ > 2 := by numbers

-- MoP Section 5.3.6 Exercise 2
example (P Q : Prop) : ¬ (P → Q) ↔ (P ∧ ¬ Q) := by
  . constructor
    intro h_not_p_implies_q
    by_cases hP : P
    . constructor
      . exact hP
      . intro hQ
        apply h_not_p_implies_q
        extra
    . constructor
      . apply False.elim
        apply h_not_p_implies_q
        intro hPP
        contradiction
      . apply False.elim
        apply h_not_p_implies_q
        intro hPP
        contradiction
    . intro h_P_and_not_Q 
      obtain ⟨hP, hQ⟩ := h_P_and_not_Q
      extra

--- Problem 5
example {p : ℕ} (k : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hk : k ∣ p) : ¬ Prime p := by
  dsimp [Prime]
  push_neg
  intro hP_ge_2
  obtain ⟨a, ha⟩ := hk
  use k
  constructor
  . use a
    apply ha
  . constructor
    . apply hk1
    . apply hkp

example {p : ℕ} (hp : ¬ Prime p) (hp2 : 2 ≤ p) : ∃ m, 2 ≤ m ∧ m < p ∧ m ∣ p := by
  have H : ¬ (∀ (m : ℕ), 2 ≤ m → m < p → ¬m ∣ p)
  · intro H
    apply hp
    apply prime_test
    . exact hp2
    . exact H
  . push_neg at H
    exact H
