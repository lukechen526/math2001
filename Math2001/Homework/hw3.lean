/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Basic
import AutograderLib

math2001_init

open Nat

/-! # Homework 3

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-3,
for clearer statements and any special instructions. -/

@[autogradedProof 2]
theorem problem1 {a b : ℚ} (h : a = 3 - b) : a + b = 3 ∨ a + b = 4 := by
  left
  rw [h]
  ring

@[autogradedProof 5]
theorem problem2 {t : ℚ} (h : t ^ 2 + t - 6 = 0) : t = 2 ∨ t = -3 := by
  have h' : t ^ 2 + t - 6 = (t - 2) * (t + 3) := by ring
  rw [h'] at h
  rw [_root_.mul_eq_zero] at h
  obtain h | h := h
  · left
    addarith [h]
  · right
    addarith [h]

@[autogradedProof 3]
theorem problem3 : ∃ a b : ℕ, a ≠ 0 ∧ 2 ^ a = 5 * b + 1 := by
  use 4, 3
  constructor
  · numbers
  · numbers

@[autogradedProof 5]
theorem problem4 (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  by_cases hx : x ≤ 0
  · use 1
    calc
      (1 : ℚ) ^ 2 = 1 := by numbers
      _ > 0 := by numbers
      _ ≥ x := by addarith [hx]
  · push_neg at hx
    by_cases hx2 : x ≤ 1
    · use 2
      calc
        (2 : ℚ) ^ 2 = 4 := by numbers
        _ > 1 := by numbers
        _ ≥ x := by addarith [hx2]
    · push_neg at hx2
      use x
      rw [pow_two]
      calc
        x * x > 1 * x := mul_lt_mul_of_pos_right hx2 hx
        _ = x := one_mul x

@[autogradedProof 5]
theorem problem5 {x : ℕ} (hx : Odd x) : Odd (x ^ 3) := by
  rw [Odd] at hx
  obtain ⟨k, hk⟩ := hx
  rw [Odd]
  use 4 * k ^ 3 + 6 * k ^ 2 + 3 * k
  rw [hk]
  ring

@[autogradedProof 5]
theorem problem6 (n : ℕ) : ∃ m ≥ n, Odd m := by
  use 2 * n + 1
  constructor
  · have h1 : n + 1 ≥ 0 := by extra
    calc
      2 * n + 1 = n + (n + 1) := by ring
      _ ≥ n + 0 := by addarith [h1]
      _ = n := by ring
  · rw [Odd] -- Proves Odd (2 * n + 1)
    use n
    ring
