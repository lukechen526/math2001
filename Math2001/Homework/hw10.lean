/- Copyright (c) Heather Macbeth, 2023-4.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq
import AutograderLib

math2001_init
set_option quotPrecheck false


/-! # Homework 10

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-10,
for clearer statements and any special instructions. -/


/- Problem 1: prove one of these, delete the other -/

@[autogradedProof 4]
theorem problem1a : { m : ℤ | m ≥ 10 } ⊆ { n : ℤ | n ^ 3 - 6 * n ^ 2 ≥ 4 * n } := by
  intro x hx
  dsimp
  have hx10 : x ≥ 10 := hx
  have h_poly_ge_0 : x ^ 2 - 6 * x - 4 ≥ 0 := by
    have h_factor_poly : x ^ 2 - 6 * x - 4 = (x - 10) * (x + 4) + 36 := by ring
    rw [h_factor_poly]
    have h_prod_ge_0 : (x - 10) * (x + 4) ≥ 0 := by
      have h1 : x - 10 ≥ 0 := by addarith [hx10]
      have h2 : x + 4 > 0 := by addarith [hx10]
      calc
        (x - 10) * (x + 4) ≥ 0 * (x + 4) := by rel [h1]
        _ = 0 := by ring
    addarith [h_prod_ge_0]
  have h_ge_0 : x * (x ^ 2 - 6 * x - 4) ≥ 0 := by
    have h1 : x ≥ 0 := by addarith [hx10]
    calc
      x * (x ^ 2 - 6 * x - 4) ≥ 0 * (x ^ 2 - 6 * x - 4) := by rel [h1]
      _ = 0 := by ring
  have h_final : x ^ 3 - 6 * x ^ 2 - 4 * x ≥ 0 := by
    have h_factor : x ^ 3 - 6 * x ^ 2 - 4 * x = x * (x ^ 2 - 6 * x - 4) := by ring
    rw [h_factor]
    exact h_ge_0
  addarith [h_final]


/- Problem 2: prove one of these, delete the other -/

@[autogradedProof 3]
theorem problem2b : { t : ℝ | t ^ 2 - 3 * t + 2 = 0 } ≠ { s : ℝ | s = 2 } := by
  intro h
  have h1 : 1 ∈ { t : ℝ | t ^ 2 - 3 * t + 2 = 0 } := by
    dsimp
    ring
  have h2 : 1 ∉ { s : ℝ | s = 2 } := by
    dsimp
    numbers
  rw [h] at h1
  contradiction


/- Problem 3: prove one of these, delete the other -/

@[autogradedProof 3]
theorem problem3a : {1, 2, 3} ∩ {2, 3, 4} ⊆ {2, 3, 6} := by
  intro x hx
  dsimp at *
  obtain ⟨(h1 | h2 | h3), (h4 | h5 | h6)⟩ := hx
  · have : 1 = 2 := by
      calc
        1 = x := by rel [h1]
        _ = 2 := by rel [h4]
    numbers at this
  · have : 1 = 3 := by
      calc
        1 = x := by rel [h1]
        _ = 3 := by rel [h5]
    numbers at this
  · have : 1 = 4 := by
      calc
        1 = x := by rel [h1]
        _ = 4 := by rel [h6]
    numbers at this
  · left
    assumption
  · have : 2 = 3 := by
      calc
        2 = x := by rel [h2]
        _ = 3 := by rel [h5]
    numbers at this
  · have : 2 = 4 := by
      calc
        2 = x := by rel [h2]
        _ = 4 := by rel [h6]
    numbers at this
  · right; left; assumption
  · right; left; assumption
  · have : 3 = 4 := by
      calc
        3 = x := by rel [h3]
        _ = 4 := by rel [h6]
    numbers at this

@[autogradedProof 4]
theorem problem4 : { r : ℤ | r ≡ 11 [ZMOD 15] }
    = { s : ℤ | s ≡ 2 [ZMOD 3] } ∩ { t : ℤ | t ≡ 1 [ZMOD 5] } := by
  ext x
  dsimp
  constructor
  · intro h
    constructor
    · obtain ⟨k, hk⟩ := h
      use 5 * k + 3
      calc
        x - 2 = (x - 11) + 9 := by ring
        _ = 15 * k + 9 := by rw [hk]
        _ = 3 * (5 * k + 3) := by ring
    · obtain ⟨k, hk⟩ := h
      use 3 * k + 2
      calc
        x - 1 = (x - 11) + 10 := by ring
        _ = 15 * k + 10 := by rw [hk]
        _ = 5 * (3 * k + 2) := by ring
  · intro h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨k, hk⟩ := h1
    obtain ⟨l, hl⟩ := h2
    use 2 * k - 3 * l
    calc
      x - 11 = 10 * (x - 2) - 9 * (x - 1) := by ring
      _ = 10 * (3 * k) - 9 * (5 * l) := by rw [hk, hl]
      _ = 30 * k - 45 * l := by ring
      _ = 15 * (2 * k - 3 * l) := by ring

/-! ### Problem 5 starts here -/


local infix:50 "∼" => fun (a b : ℤ) ↦ ∃ m n, m > 0 ∧ n > 0 ∧ a * m = b * n


/- Problem 5.1: prove one of these, delete the other -/

@[autogradedProof 2]
theorem problem51a : Reflexive (· ∼ ·) := by
  sorry

@[autogradedProof 2]
theorem problem51b : ¬ Reflexive (· ∼ ·) := by
  sorry


/- Problem 5.2: prove one of these, delete the other -/

@[autogradedProof 2]
theorem problem52a : Symmetric (· ∼ ·) := by
  sorry

@[autogradedProof 2]
theorem problem52b : ¬ Symmetric (· ∼ ·) := by
  sorry


/- Problem 5.3: prove one of these, delete the other -/

@[autogradedProof 2]
theorem problem53a : AntiSymmetric (· ∼ ·) := by
  sorry

@[autogradedProof 2]
theorem problem53b : ¬ AntiSymmetric (· ∼ ·) := by
  sorry


/- Problem 5.4: prove one of these, delete the other -/

@[autogradedProof 2]
theorem problem54a : Transitive (· ∼ ·) := by
  sorry

@[autogradedProof 2]
theorem problem54b : ¬ Transitive (· ∼ ·) := by
  sorry



/-! ### Problem 6 starts here -/

infix:50 "≺" => fun ((x1, y1) : ℝ × ℝ) (x2, y2) ↦ (x1 ≤ x2 ∧ y1 ≤ y2)


/- Problem 6.1: prove one of these, delete the other -/

@[autogradedProof 2]
theorem problem61a : Reflexive (· ≺ ·) := by
  sorry

@[autogradedProof 2]
theorem problem61b : ¬ Reflexive (· ≺ ·) := by
  sorry


/- Problem 6.2: prove one of these, delete the other -/

@[autogradedProof 2]
theorem problem62a : Symmetric (· ≺ ·) := by
  sorry

@[autogradedProof 2]
theorem problem62b : ¬ Symmetric (· ≺ ·) := by
  sorry


/- Problem 6.3: prove one of these, delete the other -/

@[autogradedProof 2]
theorem problem63a : AntiSymmetric (· ≺ ·) := by
  sorry

@[autogradedProof 2]
theorem problem63b : ¬ AntiSymmetric (· ≺ ·) := by
  sorry


/- Problem 6.4: prove one of these, delete the other -/

@[autogradedProof 2]
theorem problem64a : Transitive (· ≺ ·) := by
  sorry

@[autogradedProof 2]
theorem problem64b : ¬ Transitive (· ≺ ·) := by
  sorry
