/- Copyright (c) Heather Macbeth, 2024.  All rights reserved. -/
import Mathlib.Tactic.GCongr
import Library.Basic
import AutograderLib

macro_rules | `(tactic| gcongr_discharger) => `(tactic| numbers)
math2001_init

namespace Nat

/-! # Homework 8

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-8,
for clearer statements and any special instructions. -/


def B : ℕ → ℚ
  | 0 => 0
  | n + 1 => B n + (n + 1 : ℚ) ^ 2

@[autogradedProof 4]
theorem problem1 (n : ℕ) : B n = n * (n + 1) * (2 * n + 1) / 6 := by
  simple_induction n with k IH
  · -- base case
    dsimp [B]
    numbers
  · -- induction step
    dsimp [B]
    rw [IH]
    ring


def S : ℕ → ℚ
  | 0 => 1
  | n + 1 => S n + 1 / 2 ^ (n + 1)

@[autogradedProof 4]
theorem problem2 (n : ℕ) : S n = 2 - 1 / 2 ^ n := by
  simple_induction n with k IH
  · -- base case
    dsimp [S]
    numbers
  · -- induction step
    dsimp [S]
    rw [IH]
    ring


def a : ℕ → ℤ
  | 0 => 4
  | n + 1 => 3 * a n - 5

@[autogradedProof 4]
theorem problem3 : forall_sufficiently_large (n : ℕ), a n ≥ 10 * 2 ^ n := by
  use 5
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    dsimp [a]
    numbers
  · -- induction step
    dsimp [a]
    calc
      a (k + 1) = 3 * a k - 5 := by rw [a]
      _ ≥ 3 * (10 * 2 ^ k) - 5 := by rel [IH]
      _ = 30 * 2 ^ k - 5 := by ring
      _ = 10 * 2 ^ (k + 1) + 10 * 2 ^ k - 5 := by ring
      _ ≥ 10 * 2 ^ (k + 1) + 10 * 2 ^ 5 - 5 := by rel [hk]
      _ = 10 * 2 ^ (k + 1) + 315 := by ring
      _ ≥ 10 * 2 ^ (k + 1) := by extra

def c : ℕ → ℤ
  | 0 => 3
  | 1 => 2
  | n + 2 => 4 * c n

@[autogradedProof 4]
theorem problem4 (n : ℕ) : c n = 2 * 2 ^ n + (-2) ^ n := by
  two_step_induction n with k IH1 IH2
  · -- base case 0
    dsimp [c]
    numbers
  · -- base case 1
    dsimp [c]
    numbers
  · -- induction step
    calc
      c (k + 2) = 4 * c k := by rw [c]
      _ = 4 * (2 * 2 ^ k + (-2) ^ k) := by rw [IH1]
      _ = 2 * 2 ^ (k + 2) + 4 * (-2) ^ k := by ring
      _ = 2 * 2 ^ (k + 2) + (-2) ^ 2 * (-2) ^ k := by ring
      _ = 2 * 2 ^ (k + 2) + (-2) ^ (k + 2) := by ring


def q : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | n + 2 => 2 * q (n + 1) - q n + 6 * n + 6

@[autogradedProof 4]
theorem problem5 (n : ℕ) : q n = (n:ℤ) ^ 3 + 1 := by
  two_step_induction n with k IH1 IH2
  · -- base case 0
    dsimp [q]
    numbers
  · -- base case 1
    dsimp [q]
    numbers
  · -- induction step
    calc
      q (k + 2) = 2 * q (k + 1) - q k + 6 * k + 6 := by rw [q]
      _ = 2 * (((k + 1):ℤ) ^ 3 + 1) - ((k:ℤ) ^ 3 + 1) + 6 * k + 6 := by rw [IH1, IH2]
      _ = ((k:ℤ) + 2) ^ 3 + 1 := by ring


@[autogradedProof 5]
theorem problem6 (n : ℕ) (hn : 0 < n) : ∃ a x, Odd x ∧ n = 2 ^ a * x := by
  obtain h_even | h_odd := even_or_odd n
  · -- n is even
    obtain ⟨m, hm⟩ := h_even
    have h_pos : 0 < m := by addarith [hn, hm]
    have IH := problem6 m h_pos
    obtain ⟨a, x, h_odd_x, h_m_eq⟩ := IH
    use a + 1, x
    constructor
    · apply h_odd_x
    · calc
        n = 2 * m := hm
        _ = 2 * (2 ^ a * x) := by rw [h_m_eq]
        _ = 2 ^ (a + 1) * x := by ring
  · -- n is odd
    use 0, n
    constructor
    · apply h_odd
    · ring
