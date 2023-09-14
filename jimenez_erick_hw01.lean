import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel

--Problem 3

-- Page 21 of Lecture Slides 02
lemma Problem3a {p q r : Prop} (h1 : (p ∧ q) → r ) : p → (q → r) := by
  intro hp hq
  apply h1
  exact ⟨hp , hq⟩   

-- Page 23 of Lecture Slides 02
lemma Problem3b {p q r : Prop} (h1 : p → (q → r)) : (p → q) → (p → r) := by
  intro h_p_imp_q
  intro hp
  apply h1
  apply hp
  apply h_p_imp_q
  apply hp

-- Page 24 of Lecture Slides 02
axiom notnotE {p : Prop} (h : ¬¬p) : p
lemma Problem3c {p q r : Prop} (h1 : (p ∧ ¬q) → r) (h2 : ¬r) (h3 : p) : q := by
  have notr : ¬r := by  
    exact h2
  have notq_imp_r : ¬q → r := by
    intro notq
    apply h1 ⟨h3, notq⟩
  have notqcontradiction : ¬q → False  := by
    intro notq
    apply notr
    apply notq_imp_r
    apply notq
  have notnotq : ¬¬q := by
    apply notqcontradiction 
  apply notnotE notnotq  

-- Problem 4

-- Example 1.3.1
example {a b : ℤ} (h1 : a = 2 * b + 5) (h2 : b = 3) : a = 11 :=
  calc
    a = 2 * 3 + 5 := by rw [h1, h2]
    _ = 11 := by ring


-- Example 1.3.2
example {x : ℤ} (h1 : x + 4 = 2) : x = -2 :=
  calc
    x = x + 4 - 4 := by ring
    _ = 2 - 4 := by rw [h1]
    _= -2 := by ring

-- Example 1.3.3
example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 :=
calc
  a = a - 5 * b + 5 * b := by ring
  _ = 4 + 5 * b := by rw [h1]
  _ = -6 + 5 * (b + 2) := by ring
  _ = -6 + 5 * 3 := by rw [h2]
  _ = 9 := by ring



  
