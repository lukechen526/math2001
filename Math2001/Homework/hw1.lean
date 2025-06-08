/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import AutograderLib

math2001_init

set_option linter.unusedVariables false

/-! # Homework 1

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-1,
for clearer statements and any special instructions. -/


@[autogradedProof 5]
theorem problem1 {p q : ℤ} (h1 : p + 4 * q = 1) (h2 : q - 1 = 2) : p = -11 := by
  have h3 : q = 3 := by addarith [h2]
  have h4 : p + 4 * 3 = 1 := by rw [h3] at h1; exact h1
  addarith [h4]

@[autogradedProof 5]
theorem problem2 {a b : ℝ} (h1 : a + 2 * b = 4) (h2 : a - b = 1) : a = 2 := by
  have h3 : 3 * a = 6 := by
    calc
      3 * a = (a + 2 * b) + 2 * (a - b) := by ring
      _ = 4 + 2 * 1 := by rw [h1, h2]
      _ = 6 := by numbers
  calc
    a = 3 *a / 3 := by ring
    _ = 6 / 3 := by rw [h3]
    _ = 2 := by numbers

@[autogradedProof 5]
theorem problem3 {x : ℤ} (hx : x ≥ 9) : x ^ 3 - 8 * x ^ 2 + 2 * x ≥ 3 := by
  have h1 : x ^ 2 - 8 * x + 2 ≥ 11 :=
    calc
      x ^ 2 - 8 * x + 2 = x * (x - 8) + 2 := by ring
      _ ≥ 9 * (9 - 8) + 2 := by rel [hx]
      _ = 11 := by numbers
  have h2 : x ^ 3 - 8 * x ^ 2 + 2 * x ≥ 99 :=
    calc
      x ^ 3 - 8 * x ^ 2 + 2 * x = x * (x ^ 2 - 8 * x + 2) := by ring
      _ ≥ 9 * 11 := by rel [hx, h1]
      _ = 99 := by numbers
  addarith [h2]

@[autogradedProof 5]
theorem problem4 {x : ℚ} : x ^ 2 - 2 * x ≥ -1 := by
  have h: x^2 - 2*x + 1 ≥ 0 := by
    calc
      x^2 - 2*x + 1 = (x-1)^2 := by ring
      _ ≥ 0 := by apply sq_nonneg
  addarith[h]

@[autogradedProof 5]
theorem problem5 (a b : ℝ) (h1 : -b ≤ a) (h2 : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  have h3 : 0 ≤ b - a := by addarith [h2]
  have h4 : 0 ≤ b + a := by addarith [h1]
  have h5 : 0 ≤ (b - a) * (b + a) := by
    apply mul_nonneg h3 h4
  have h6 : b ^ 2 - a ^ 2 = (b - a) * (b + a) := by ring
  rw [← h6] at h5
  addarith [h5]
