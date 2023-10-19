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


-- MoP Subsection 5.1.7 Exercise 11
example {P Q : α → Prop} (h : ∀ x, P x ↔ Q x) : (∃ x, P x) ↔ (∃ x, Q x) := by
  constructor
  . intro hP
    obtain ⟨a, hPa⟩ := hP
    use a
    have hPaQa := by apply h a
    exact hPaQa.mp hPa
  . intro hQ
    obtain ⟨a, hQa⟩ := hQ
    use a
    have hQaPa := by apply h a
    exact hQaPa.mpr hQa

-- MoP Subsection 5.1.7 Exercise 12
example (P : α → β → Prop) : (∃ x y, P x y) ↔ ∃ y x, P x y := by
  constructor
  . intro hPP
    extra
  . intro hPP
    extra

-- MoP Subsection 5.1.7 Exercise 13
example (P : α → β → Prop) : (∀ x y, P x y) ↔ ∀ y x, P x y := by
  constructor
  . intro hP
    intros a b
    apply hP b a
  . intro hP
    intros a b
    apply hP b a

-- MoP Subsection 5.1.7 Exercise 14
example (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  constructor
  . intro hPQ
    obtain ⟨hPx, hQ⟩ := hPQ
    obtain ⟨a, hPa⟩ := hPx
    use a
    constructor
    . apply hPa
    . apply hQ
  . intro hPQ
    obtain ⟨a, hPaQ⟩ := hPQ
    obtain ⟨hPa, hQ⟩ := hPaQ
    constructor
    . use a
      exact hPa
    . exact hQ
 
--- Problem 5

-- MoP Subsection 5.2.7 Exercise 1
def Tribalanced (x : ℝ) : Prop := ∀ n : ℕ, (1 + x / n) ^ n < 3

example : ∃ x : ℝ, Tribalanced x ∧ ¬ Tribalanced (x + 1) := by
  by_cases hT1 : Tribalanced 1
  . use 1
    constructor
    . apply hT1
    . dsimp [Tribalanced]
      simp
      use 1
      simp
      numbers
  . use 0
    constructor
    . dsimp [Tribalanced]
      simp
      numbers
    . simp
      apply hT1

def Superpowered (k : ℕ) : Prop := ∀ n : ℕ, Prime (k ^ k ^ n + 1)

-- MoP Subsection 5.2.7 Exercise 3
example : ∃ k : ℕ, Superpowered k ∧ ¬ Superpowered (k + 1) := by
  use 1
  constructor
  . dsimp [Superpowered]
    simp
    numbers
    apply prime_two
  . numbers
    dsimp [Superpowered]
    simp
    use 5
    numbers
    dsimp [Prime]
    simp
    use 641
    constructor
    simp
    simp
