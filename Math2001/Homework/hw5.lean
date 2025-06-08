/- Copyright (c) Heather Macbeth, 2023-4.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq
import AutograderLib

math2001_init

/-! # Homework 5

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-5,
for clearer statements and any special instructions. -/

@[autogradedProof 2]
theorem problem1 : ∃ k : ℤ, k > 10 ∧ 3 * k ≡ 2 [ZMOD 5] ∧ k ∣ 72 := by
  use 24
  constructor
  · numbers
  · constructor
    · dsimp [Int.ModEq]
      use 14
      numbers
    · use 3
      numbers

@[autogradedProof 3]
theorem problem2 {a : ℤ} (ha : a ≡ 4 [ZMOD 5]) :
    a ^ 3 + 2 * a ^ 2 + 3 ≡ 4 [ZMOD 5] := by
  calc
    a ^ 3 + 2 * a ^ 2 + 3 ≡ 4 ^ 3 + 2 * 4 ^ 2 + 3 [ZMOD 5] := by rel [ha]
    _ = 99 := by numbers
    _ ≡ 4 [ZMOD 5] := by
      dsimp [Int.ModEq]
      use 19
      numbers

/-
The proof uses a `calc` block to show the modular equivalence.
It first substitutes `a` with `4` using the hypothesis `a ≡ 4 [ZMOD 5]`.
Then it computes the numerical value and shows it is congruent to `4` modulo `5`.
-/

/-
The proof provides the witness `k = 24` for the existential statement.
It then proves the three required properties: `24 > 10`, `3 * 24 ≡ 2 [ZMOD 5]`,
and `24 ∣ 72` by providing witnesses and using the `numbers` tactic.
-/

@[autogradedProof 5]
theorem problem3 {x : ℤ} : x ^ 5 ≡ x [ZMOD 5] := by
  mod_cases hx : x % 5
  · calc
      x ^ 5 ≡ 0 ^ 5 [ZMOD 5] := by rel [hx]
      _ = 0 := by numbers
      _ ≡ x [ZMOD 5] := by rel [hx]
  · calc
      x ^ 5 ≡ 1 ^ 5 [ZMOD 5] := by rel [hx]
      _ = 1 := by numbers
      _ ≡ x [ZMOD 5] := by rel [hx]
  · calc
      x ^ 5 ≡ 2 ^ 5 [ZMOD 5] := by rel [hx]
      _ = 32 := by numbers
      _ ≡ 2 [ZMOD 5] := by
        dsimp [Int.ModEq]
        use 6
        numbers
      _ ≡ x [ZMOD 5] := by rel [hx]
  · calc
      x ^ 5 ≡ 3 ^ 5 [ZMOD 5] := by rel [hx]
      _ = 243 := by numbers
      _ ≡ 3 [ZMOD 5] := by
        dsimp [Int.ModEq]
        use 48
        numbers
      _ ≡ x [ZMOD 5] := by rel [hx]
  · calc
      x ^ 5 ≡ 4 ^ 5 [ZMOD 5] := by rel [hx]
      _ = 1024 := by numbers
      _ ≡ 4 [ZMOD 5] := by
        dsimp [Int.ModEq]
        use 204
        numbers
      _ ≡ x [ZMOD 5] := by rel [hx]

/-
The proof uses `mod_cases` to handle the 5 possible values of `x % 5`.
For each case (`0` through `4`), it uses a `calc` block to show that
`x ^ 5` is congruent to that value, and thus to `x`, modulo `5`.
-/

@[autogradedProof 3]
theorem problem4 {a : ℚ} (h : ∀ b : ℚ, a + b ^ 2 ≥ 0) : a ≥ 0 := by
  have h_b0 : a + 0 ^ 2 ≥ 0 := h 0
  addarith [h_b0]

/-
The proof specializes the universal hypothesis `h` with `b = 0`.
This yields `a + 0 ^ 2 ≥ 0`, which simplifies to the goal `a ≥ 0`.
The `addarith` tactic is used for the final step.
-/

@[autogradedProof 5]
theorem problem5 (n : ℕ) (h : ∀ a : ℕ, 6 ≤ a → a ≤ 10 → a ∣ n) :
    ∀ b : ℕ, 1 ≤ b → b ≤ 5 → b ∣ n := by
  intro b hb1 hb5
  have h6 : 6 ∣ n := h 6 (by numbers) (by numbers)
  have h8 : 8 ∣ n := h 8 (by numbers) (by numbers)
  have h9 : 9 ∣ n := h 9 (by numbers) (by numbers)
  have h10 : 10 ∣ n := h 10 (by numbers) (by numbers)
  interval_cases b
  · apply one_dvd
  · obtain ⟨k, hk⟩ := h6; use k * 3; rw [hk]; ring
  · obtain ⟨k, hk⟩ := h9; use k * 3; rw [hk]; ring
  · obtain ⟨k, hk⟩ := h8; use k * 2; rw [hk]; ring
  · obtain ⟨k, hk⟩ := h10; use k * 2; rw [hk]; ring

/-
The proof first establishes that `n` is divisible by `6, 8, 9, 10` from the hypothesis.
Then, it uses `interval_cases` to handle each value of `b` from `1` to `5`.
For each case, it shows `b ∣ n` by using the divisibility facts previously established.
-/

@[autogradedProof 3]
theorem problem6 : ∃ a : ℝ, ∀ b : ℝ, a ≤ b ^ 2 := by
  use 0
  intro b
  exact sq_nonneg b

/-
The proof provides the witness `a = 0` for the existential statement.
The remaining goal `∀ b : ℝ, 0 ≤ b ^ 2` is then proven by introducing `b`
and applying the standard library lemma `sq_nonneg`.
-/

@[autogradedProof 4]
theorem problem7 : forall_sufficiently_large x : ℝ, x ^ 3 - 5 * x ≥ 11 * x ^ 2 := by
  dsimp
  use 12
  intro x hx
  have h_nonneg : x * (x - 11) - 5 ≥ 0 := by
    have h1 : x - 11 ≥ 1 := by addarith [hx]
    have h2 : x ≥ 12 := by addarith [hx]
    calc
      x * (x - 11) - 5 ≥ 12 * 1 - 5 := by rel [h1, h2]
      _ = 7 := by numbers
      _ ≥ 0 := by numbers
  calc
    x ^ 3 - 5 * x = x * x ^ 2 - 5 * x := by ring
    _ = x * (x ^ 2 - 5) := by ring
    _ ≥ 11 * x ^ 2 := by
      rw [ge_iff_le] -- Add this line to change the goal to ≤ form
      rw [← sub_nonneg]
      calc
        x * (x ^ 2 - 5) - 11 * x ^ 2 = x * (x ^ 2 - 5 - 11 * x) := by ring
        _ = x * (x * (x - 11) - 5) := by ring
        _ ≥ 0 := by
          have hx_pos : x > 0 := by addarith[hx]
          apply mul_nonneg
          · apply le_of_lt; exact hx_pos
          · exact h_nonneg

/-
The proof provides a witness `N = 12` for the "sufficiently large" condition.
For `x ≥ 12`, the inequality is rearranged to `x * (x * (x - 11) - 5) ≥ 0`.
The proof then shows that both factors are non-negative: `x` is positive,
and `x * (x - 11) - 5` is shown to be non-negative via a `calc` block.
-/
