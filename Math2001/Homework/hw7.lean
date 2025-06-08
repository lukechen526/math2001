/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq
import AutograderLib

math2001_init


/-! # Homework 7

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-7,
for clearer statements and any special instructions. -/


@[autogradedProof 5]
theorem problem1 (P Q : Prop) : ¬ (P → Q) ↔ (P ∧ ¬ Q) := by
  constructor
  · intro h
    by_cases hP : P
    · constructor
      · exact hP
      · intro hQ
        apply h
        intro hP_proof
        exact hQ
    · exfalso
      apply h
      intro hP_proof
      have h_neg_p := hP
      contradiction
  · intro h
    obtain ⟨hP, hnQ⟩ := h
    intro hPQ
    apply hnQ
    apply hPQ
    apply hP

@[autogradedProof 3]
theorem problem2 : ¬ (∀ x : ℚ, 2 * x ^ 2 ≥ x) := by
  push_neg
  use 1/4
  numbers

@[autogradedProof 4]
theorem problem3 (n : ℕ) : 6 ^ n ≡ 1 [ZMOD 7] ∨ 6 ^ n ≡ 6 [ZMOD 7] := by
  two_step_induction n with k IH1 IH2
  · left
    numbers
  · right
    numbers
  · obtain h | h := IH2
    · right
      calc
        6 ^ (k + 2) = 6 * 6 ^ (k + 1) := by rw [pow_succ]
        _ ≡ 6 * 1 [ZMOD 7] := by rel [h]
        _ = 6 := by ring
    · left
      calc
        6 ^ (k + 2) = 6 * 6 ^ (k + 1) := by rw [pow_succ]
        _ ≡ 6 * 6 [ZMOD 7] := by rel [h]
        _ = 36 := by numbers
        _ ≡ 1 + 7 * 5 [ZMOD 7] := by numbers
        _ ≡ 1 [ZMOD 7] := by extra

@[autogradedProof 4]
theorem problem4 (n : ℕ) :
    4 ^ n ≡ 1 [ZMOD 7] ∨ 4 ^ n ≡ 2 [ZMOD 7] ∨ 4 ^ n ≡ 4 [ZMOD 7] := by
  match n with
  | 0 => left; numbers
  | 1 => right; right; numbers
  | 2 =>
    right
    left
    calc
      4 ^ 2 ≡ 16 [ZMOD 7] := by numbers
      _ ≡ 2 + 7 * 2 [ZMOD 7] := by numbers
      _ ≡ 2 [ZMOD 7] := by extra
  | k + 1 =>
    have IH := problem4 k
    rw [pow_succ]
    obtain h | h | h := IH
    · right
      right
      calc
        4 * 4 ^ k ≡ 4 * 1 [ZMOD 7] := by rel [h]
        _ = 4 := by ring
    · left
      calc
        4 * 4 ^ k ≡ 4 * 2 [ZMOD 7] := by rel [h]
        _ = 8 := by ring
        _ ≡ 1 + 1 * 7 [ZMOD 7] := by numbers
        _ ≡ 1 [ZMOD 7] := by extra
    · right
      left
      calc
        4 * 4 ^ k ≡ 4 * 4 [ZMOD 7] := by rel [h]
        _ = 16 := by ring
        _ ≡ 2 + 2 * 7 [ZMOD 7] := by numbers
        _ ≡ 2 [ZMOD 7] := by extra

@[autogradedProof 5]
theorem problem5 {a : ℝ} (ha : -1 ≤ a) : ¬ ∃ n : ℕ, (1 + a) ^ n < 1 + n * a := by
  push_neg
  intro n
  simple_induction n with k IH
  · calc
      1 + 0 * a = 1 := by ring
      _ ≤ (1 + a) ^ 0 := by rw [pow_zero]
  · have h_a_ge_0 : 1 + a ≥ 0 := by addarith [ha]
    calc
      (1 + a) ^ (k + 1) = (1 + a) * (1 + a) ^ k := by ring
      _ ≥ (1 + a) * (1 + k * a) := by rel [IH]
      _ = 1 + (k + 1) * a + k * a ^ 2 := by ring
      _ ≥ 1 + (k + 1) * a := by extra

@[autogradedProof 4]
theorem problem6 : forall_sufficiently_large n : ℕ, (3:ℤ) ^ n ≥ 2 ^ n + 100 := by
  dsimp
  use 10
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · numbers
  · calc
      (3 : ℤ) ^ (k + 1) = 3 * 3 ^ k := by ring
      _ ≥ 3 * (2 ^ k + 100) := by rel [IH]
      _ = 2 * 2 ^ k + 2 ^ k + 300 := by ring
      _ = 2 ^ (k + 1) + 2 ^ k + 300 := by ring
      _ = 2 ^ (k + 1) + 100 + (2 ^ k + 200) := by ring
      _ ≥ 2 ^ (k + 1) + 100 := by extra
