/- Copyright (c) Heather Macbeth, 2024.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import AutograderLib

math2001_init

/-! # Homework 2

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-2,
for clearer statements and any special instructions. -/


@[autogradedProof 5]
theorem problem1 {x : ℚ} (h1 : x ^ 2 = 9) (h2 : 1 < x) : x = 3 := by
  have h3 : x ^ 2 = 3 ^ 2 := by
    rw [h1]
    numbers
  have h4 : x = 3 ∨ x = -3 := by
    apply sq_eq_sq_iff_eq_or_eq_neg.mp
    exact h3
  obtain h4 | h4 := h4
  · exact h4
  · have h5 : ¬(1 < x) := by
      rw [h4]
      numbers
    contradiction

@[autogradedProof 5]
theorem problem2 {s : ℚ} (h1 : 3 * s ≤ -15) (h2 : 2 * s ≥ -10) : s = -5 := by
  apply le_antisymm
  · have h3 : s ≤ -5 := by
      have h : 0 < (3 : ℚ) := by numbers
      calc
        s = 1 / 3 * (3 * s) := by ring
        _ ≤ 1 / 3 * -15 := by rel [h1]
        _ = -5 := by numbers
    exact h3
  · have h4 : -5 ≤ s := by
      have h : 0 < (2 : ℚ) := by numbers
      calc
        -5 = -10 / 2 := by numbers
        _ ≤ 2 * s / 2 := by rel [h2]
        _ = s := by ring
    exact h4

@[autogradedProof 4]
theorem problem3 {t : ℚ} (h : t = 2 ∨ t = -3) : t ^ 2 + t - 6 = 0 := by
  obtain h | h := h
  · rw [h]
    numbers
  · rw [h]
    numbers

@[autogradedProof 5]
theorem problem4 {x : ℤ} : 3 * x ≠ 10 := by
  by_contra h
  have h_mod_3 := congr_arg (fun x ↦ x % 3) h
  norm_num at h_mod_3

@[autogradedProof 6]
theorem problem5 {x y : ℝ} (h1 : 2 ≤ x ∨ 2 ≤ y) (h2 : x ^ 2 + y ^ 2 = 4) :
    x ^ 2 * y ^ 2 = 0 := by
  obtain h | h := h1
  · have hx_sq_ge_4 : 4 ≤ x ^ 2 := by
      calc
        4 = 2 ^ 2 := by numbers
        _ ≤ x ^ 2 := by
          have h_pos : 0 ≤ (2:ℝ) := by numbers
          exact pow_le_pow_of_le_left h_pos h 2
    have hy_sq_le_0 : y ^ 2 ≤ 0 := by
      calc
        y ^ 2 = 4 - x ^ 2 := by
          rw [← h2]
          ring
        _ ≤ 4 - 4 := by rel [hx_sq_ge_4]
        _ = 0 := by numbers
    have hy_sq_eq_0 : y ^ 2 = 0 := by
      apply le_antisymm
      · exact hy_sq_le_0
      · exact sq_nonneg y
    rw [hy_sq_eq_0]
    ring
  · have hy_sq_ge_4 : 4 ≤ y ^ 2 := by
      calc
        4 = 2 ^ 2 := by numbers
        _ ≤ y ^ 2 := by
          have h_pos : 0 ≤ (2:ℝ) := by numbers
          exact pow_le_pow_of_le_left h_pos h 2
    have hx_sq_le_0 : x ^ 2 ≤ 0 := by
      calc
        x ^ 2 = 4 - y ^ 2 := by
          rw [← h2]
          ring
        _ ≤ 4 - 4 := by rel [hy_sq_ge_4]
        _ = 0 := by numbers
    have hx_sq_eq_0 : x ^ 2 = 0 := by
      apply le_antisymm
      · exact hx_sq_le_0
      · exact sq_nonneg x
    rw [hx_sq_eq_0]
    ring
