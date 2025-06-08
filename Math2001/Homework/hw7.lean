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
  | k + 3 =>
    have IH := problem4 k
    rw [pow_add, pow_three]
    obtain h | h | h := IH
    · left
      rel [h]
      numbers
    · right
      right
      rel [h]
      numbers
    · right
      left
      rel [h]
      numbers

@[autogradedProof 5]
theorem problem5 {a : ℝ} (ha : -1 ≤ a) : ¬ ∃ n : ℕ, (1 + a) ^ n < 1 + n * a := by
  push_neg
  sorry

@[autogradedProof 4]
theorem problem6 : forall_sufficiently_large n : ℕ, (3:ℤ) ^ n ≥ 2 ^ n + 100 := by
  dsimp
  sorry
