/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Basic
import Library.Theory.ModEq.Defs
import Library.Tactic.ModCases
import Library.Theory.ParityModular
import AutograderLib

math2001_init

open Int

/-! # Homework 4

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-4,
for clearer statements and any special instructions. -/

@[autogradedProof 5]
theorem problem1 (n : ℤ) : Odd (3 * n ^ 2 + 3 * n - 1) := by
  obtain ⟨k, hk⟩ | ⟨k, hk⟩ := Int.even_or_odd n
  · rw [hk]
    use 6 * k ^ 2 + 3 * k - 1
    ring
  · rw [hk]
    use 6 * k ^ 2 + 9 * k + 2
    ring

@[autogradedProof 1]
theorem problem2 : (8 : ℤ) ∣ 96 := by
  use 12
  numbers

@[autogradedProof 2]
theorem problem3 : ¬(8 : ℤ) ∣ -55 := by
  intro h
  obtain ⟨k, hk⟩ := h
  have h_lt1 : 8 * -7 < -55 := by numbers
  have h_lt2 : -55 < 8 * -6 := by numbers
  rw [hk] at h_lt1
  rw [hk] at h_lt2
  cancel 8 at h_lt1
  cancel 8 at h_lt2
  have h_ge_k : k ≥ -6 := by addarith [h_lt1]
  have h_le_k : k ≤ -7 := by addarith [h_lt2]
  have : -6 ≤ -7 := by
    calc
      -6 ≤ k := h_ge_k
      _ ≤ -7 := h_le_k
  numbers at this

@[autogradedProof 4]
theorem problem4 {a b c : ℤ} (hab : a ^ 3 ∣ b) (hbc : b ^ 2 ∣ c) : a ^ 6 ∣ c := by
  obtain ⟨k, hk⟩ := hab
  obtain ⟨l, hl⟩ := hbc
  use k ^ 2 * l
  calc
    c = b ^ 2 * l := by rw [hl]
    _ = (a ^ 3 * k) ^ 2 * l := by rw [hk]
    _ = a ^ 6 * (k ^ 2 * l) := by ring

@[autogradedProof 1]
theorem problem5 : 31 ≡ 13 [ZMOD 3] := by
  use 6
  numbers

@[autogradedProof 2]
theorem problem6 : ¬(51 ≡ 62 [ZMOD 5]) := by
  intro h
  dsimp [ModEq] at h
  have h' : 5 ∣ -11 := by
    rw [show -11 = 51 - 62 by numbers]
    exact h
  obtain ⟨k, hk⟩ := h'
  have h_lt1 : 5 * -3 < -11 := by numbers
  have h_lt2 : -11 < 5 * -2 := by numbers
  rw [hk] at h_lt1
  rw [hk] at h_lt2
  cancel 5 at h_lt1
  cancel 5 at h_lt2
  have h_ge_k : k ≥ -2 := by addarith [h_lt1]
  have h_le_k : k ≤ -3 := by addarith [h_lt2]
  have : -2 ≤ -3 := by
    calc
      -2 ≤ k := h_ge_k
      _ ≤ -3 := h_le_k
  numbers at this

@[autogradedProof 5]
theorem problem7 {a b n : ℤ} (h : a ≡ b [ZMOD n]) : a ^ 3 ≡ b ^ 3 [ZMOD n] := by
  obtain ⟨k, hk⟩ := h
  use k * (a ^ 2 + a * b + b ^ 2)
  calc
    a ^ 3 - b ^ 3 = (a - b) * (a ^ 2 + a * b + b ^ 2) := by ring
    _ = n * k * (a ^ 2 + a * b + b ^ 2) := by rw [hk]
    _ = n * (k * (a ^ 2 + a * b + b ^ 2)) := by ring

@[autogradedProof 5]
theorem problem8 {a b c n : ℤ} (h1 : a ≡ b [ZMOD n]) (h2 : b ≡ c [ZMOD n]) : a ≡ c [ZMOD n] := by
  obtain ⟨k, hk⟩ := h1
  obtain ⟨l, hl⟩ := h2
  use k + l
  calc
    a - c = (a - b) + (b - c) := by ring
    _ = n * k + n * l := by rw [hk, hl]
    _ = n * (k + l) := by ring
