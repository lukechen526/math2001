/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init

namespace Nat


example (n : ℕ) : 2 ^ n ≥ n + 1 := by
  simple_induction n with k IH
  · -- base case
    numbers
  · -- inductive step
    calc 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≥ 2 * (k + 1) := by rel [IH]
      _ = (k + 1 + 1) + k := by ring
      _ ≥ k + 1 + 1 := by extra


example (n : ℕ) : Even n ∨ Odd n := by
  simple_induction n with k IH
  · -- base case
    left
    dsimp [Even]
    use 0
    numbers
  · -- inductive step
    obtain ⟨x, hx⟩ | ⟨x, hx⟩ := IH
    · right
      dsimp [Odd]
      use x
      rw [hx]
    · left
      dsimp [Even]
      use x + 1
      rw [hx]
      ring

example {a b d : ℤ} (h : a ≡ b [ZMOD d]) (n : ℕ) : a ^ n ≡ b ^ n [ZMOD d] := by
  simple_induction n with k IH
  · -- base case
    calc
   a ^ 0  = 1 := by ring
    _ ≡ 1 [ZMOD d] := by extra
    _ = b ^ 0 := by ring
  · -- inductive step
    obtain ⟨x, hx⟩ := IH
    dsimp [Int.ModEq] at *
    obtain ⟨y, hy⟩ := h
    use a * x + b ^ k * y
    calc
    a ^ (k + 1) - b ^ (k + 1) = a * (a ^ k - b ^ k) + b ^ k * (a - b) := by ring
                           _ = a * (d * x) + b ^ k * (d * y) := by rw [hx, hy]
                           _ = d * (a * x + b ^ k * y) := by ring

example (n : ℕ) : 4 ^ n ≡ 1 [ZMOD 15] ∨ 4 ^ n ≡ 4 [ZMOD 15] := by
  simple_induction n with k IH
  · -- base case
    left
    numbers
  · -- inductive step
    obtain hk | hk := IH
    · right
      calc (4:ℤ) ^ (k + 1) = 4 * 4 ^ k := by ring
        _ ≡ 4 * 1 [ZMOD 15] := by rel [hk]
        _ = 4 := by numbers
    · left
      calc (4:ℤ) ^ (k + 1) = 4 * 4 ^ k := by ring
        _ ≡ 4 * 4 [ZMOD 15] := by rel [hk]
        _ = 15 * 1 + 1 := by numbers
        _ ≡ 1 [ZMOD 15] := by extra


example {n : ℕ} (hn : 2 ≤ n) : (3:ℤ) ^ n ≥ 2 ^ n + 5 := by
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    numbers
  · -- inductive step
    calc (3:ℤ) ^ (k + 1) = 2 * 3 ^ k + 3 ^ k := by ring
      _ ≥ 2 * (2 ^ k + 5) + 3 ^ k := by rel [IH]
      _ = 2 ^ (k + 1) + 5 + (5 + 3 ^ k) := by ring
      _ ≥ 2 ^ (k + 1) + 5 := by extra


example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 := by
  dsimp
  use 4
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    numbers
  · -- inductive step
    calc
      2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≥ 2 * k ^ 2 := by rel [IH]
      _ = k ^ 2 + k ^ 2 := by ring
      _ = k ^ 2 + k * k := by ring
      _ ≥ k ^ 2 + 4 * k := by rel [hk]
      _ = k ^ 2 + 2 * k + 2 * k := by ring
      _ ≥  k ^ 2 + 2 * k + 2 * 4 := by rel [hk]
      _ = (k + 1) ^ 2 + 7 := by ring
      _ ≥ (k + 1) ^ 2 := by extra

/-! # Exercises -/


example (n : ℕ) : 3 ^ n ≥ n ^ 2 + n + 1 := by
  simple_induction n with k IH
  · -- base case
    numbers
  · -- inductive step
    calc
    3 ^ (k + 1) = 3 * 3 ^ k := by ring
              _ ≥ 3 * (k ^ 2 + k + 1) := by rel [IH]
              _ = 3 * k ^ 2 + 3 * k + 3 := by ring
              _ = 2 * k ^ 2 + (k ^ 2 + 3 * k + 3) := by ring
              _ = 2 * k ^ 2 + (k ^ 2 + 2 * k + 1) + (k + 1) + 1 := by ring
              _ = 2 * k ^ 2 + (k + 1) ^ 2 + (k + 1) + 1 := by ring
              _ ≥ (k + 1) ^ 2 + (k + 1) + 1 := by extra

example {a : ℝ} (ha : -1 ≤ a) (n : ℕ) : (1 + a) ^ n ≥ 1 + n * a := by
  sorry

example (n : ℕ) : 5 ^ n ≡ 1 [ZMOD 8] ∨ 5 ^ n ≡ 5 [ZMOD 8] := by
  sorry

example (n : ℕ) : 6 ^ n ≡ 1 [ZMOD 7] ∨ 6 ^ n ≡ 6 [ZMOD 7] := by
  sorry

example (n : ℕ) :
    4 ^ n ≡ 1 [ZMOD 7] ∨ 4 ^ n ≡ 2 [ZMOD 7] ∨ 4 ^ n ≡ 4 [ZMOD 7] := by
  sorry

example : forall_sufficiently_large n : ℕ, (3:ℤ) ^ n ≥ 2 ^ n + 100 := by
  dsimp
  sorry

example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 + 4 := by
  dsimp
  sorry

example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 3 := by
  dsimp
  use 10
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    numbers
  · -- inductive step
    calc
      2 ^ (k + 1) = 2 * 2 ^ k := by ring
                _ = 2 ^ k + 2 ^ k := by ring
                _ ≥ k ^ 3 + k ^ 3 := by rel [IH]
                _ = k ^ 3 + k * k ^ 2 := by ring
                _ ≥ k ^ 3 + 10 * k ^ 2 := by rel [hk]
                _ = k ^ 3 + 3 * k ^ 2 + 7 * k ^ 2 := by ring
                _ = k ^ 3 + 3 * k ^ 2 + 7 * k * k := by ring
                _ ≥ k ^ 3 + 3 * k ^ 2 + 7 * 10 * k := by rel [hk]
                _ = k ^ 3 + 3 * k ^ 2 + 70 * k := by ring
                _ = k ^ 3 + 3 * k ^ 2 + 3 * k + 67 * k := by ring
                _ ≥ k ^ 3 + 3 * k ^ 2 + 3 * k + 67 * 10 := by rel [hk]
                _ = k ^ 3 + 3 * k ^ 2 + 3 * k + 1 + 669 := by ring
                _ ≥ k ^ 3 + 3 * k ^ 2 + 3 * k + 1 := by extra
                _ = (k + 1) ^ 3 := by ring

theorem Odd.pow {a : ℕ} (ha : Odd a) (n : ℕ) : Odd (a ^ n) := by
  dsimp [Odd] at *
  simple_induction n with k IH
  · -- base case
    use 0
    calc
      a ^ 0 = 1 := by ring
      _ = 2 * 0 + 1 := by numbers
  · -- inductive step
    obtain ⟨p, hp⟩ := ha
    obtain ⟨q, hq⟩ := IH
    use 2 * p * q + p + q
    calc
      a ^ (k + 1) = a * a ^ k := by ring
                _ = (2 * p + 1) * a ^ k := by rw [hp]
                _ = (2 * p + 1) * (2 * q + 1) := by rw [hq]
                _ = 2 * (2 * p * q + p + q) + 1 := by ring
theorem Nat.even_of_pow_even {a n : ℕ} (ha : Even (a ^ n)) : Even a := by
  by_contra h
  rw [← Nat.odd_iff_not_even] at h
  have ha' := Odd.pow h n
  rw [Nat.odd_iff_not_even] at ha'
  contradiction
