/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq
import AutograderLib

math2001_init
set_option pp.funBinderTypes true

/-! # Homework 6

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-6,
for clearer statements and any special instructions. -/

@[autogradedProof 4]
theorem problem1 : ¬ (∃ t : ℝ, t ≤ 5 ∧ 2 * t ≥ 12) := by
  intro H
  obtain ⟨t, ht1, ht2⟩ := H
  have ht3 :=
  calc 12 ≤ 2 * t := ht2
    _ ≤ 2 * 5 := by rel [ht1]
    _ = 10 := by numbers
  numbers at ht3

/-
**Human-readable proof:**

Assume, for contradiction, that there exists a real number `t` such that `t ≤ 5` and `2 * t ≥ 12`.
From `t ≤ 5`, multiplying both sides by 2 gives `2 * t ≤ 10`.
But we also have `2 * t ≥ 12`, which implies `12 ≤ 10`.
This is a contradiction since `12` is not less than or equal to `10`.
Therefore, no such `t` exists.
-/

@[autogradedProof 6]
theorem problem4 (t : ℤ) : t ^ 2 + t + 3 ≡ 0 [ZMOD 5] ↔ t ≡ 1 [ZMOD 5] ∨ t ≡ 3 [ZMOD 5] := by
  constructor
  · intro h
    mod_cases h' : t % 5
    · -- t ≡ 0 [ZMOD 5]
      have :=
      calc
        0 ≡  t ^ 2 + t + 3 [ZMOD 5] := by rel [h]
        _ ≡ 0 ^ 2 + 0 + 3 [ZMOD 5] := by rel [h']
        _ ≡ 3 [ZMOD 5] := by numbers
      numbers at this
    · -- t ≡ 1 [ZMOD 5]
      left
      apply h'
    · -- t ≡ 2 [ZMOD 5]
      have :=
      calc
        0 ≡  t ^ 2 + t + 3 [ZMOD 5] := by rel [h]
        _ ≡ 2 ^ 2 + 2 + 3 [ZMOD 5] := by rel [h']
        _ ≡ 9 [ZMOD 5] := by numbers
        _ ≡ 4 + 1 * 1* 5 [ZMOD 5] := by numbers
        _ ≡ 4 [ZMOD 5] := by extra
      numbers at this
    · -- t ≡ 3 [ZMOD 5]
      right
      apply h'
    · -- t ≡ 4 [ZMOD 5]
      have :=
      calc
        0 ≡  t ^ 2 + t + 3 [ZMOD 5] := by rel [h]
        _ ≡ 4 ^ 2 + 4 + 3 [ZMOD 5] := by rel [h']
        _ ≡ 23 [ZMOD 5] := by numbers
        _ ≡ 3 + 4 * 5 [ZMOD 5] := by numbers
        _ ≡ 3 [ZMOD 5] := by extra
      numbers at this

  · intro H
    obtain H | H := H
    · calc
        t ^ 2 + t + 3 ≡ 1 ^ 2 + 1 + 3 [ZMOD 5] := by rel [H]
        _ ≡ 1 * 5 [ZMOD 5] := by numbers
        _ ≡ 0 [ZMOD 5] := by extra
    · calc
        t ^ 2 + t + 3 ≡ 3 ^ 2 + 3 + 3 [ZMOD 5] := by rel [H]
        _ ≡ 0 + 3 * 5 [ZMOD 5] := by numbers
        _ ≡ 0 [ZMOD 5] := by extra

/-
**Human-readable proof:**

We need to show that `t^2 + t + 3 ≡ 0 [ZMOD 5]` if and only if `t ≡ 1 [ZMOD 5]` or `t ≡ 3 [ZMOD 5]`.

For the forward direction, we consider all possible residues of `t` modulo 5:
- If `t ≡ 0 [ZMOD 5]`, then `t^2 + t + 3 ≡ 3 [ZMOD 5]`, which is not 0.
- If `t ≡ 1 [ZMOD 5]`, then `t^2 + t + 3 ≡ 0 [ZMOD 5]`.
- If `t ≡ 2 [ZMOD 5]`, then `t^2 + t + 3 ≡ 4 [ZMOD 5]`, which is not 0.
- If `t ≡ 3 [ZMOD 5]`, then `t^2 + t + 3 ≡ 0 [ZMOD 5]`.
- If `t ≡ 4 [ZMOD 5]`, then `t^2 + t + 3 ≡ 3 [ZMOD 5]`, which is not 0.

Thus, `t^2 + t + 3 ≡ 0 [ZMOD 5]` only when `t ≡ 1 [ZMOD 5]` or `t ≡ 3 [ZMOD 5]`.

For the reverse direction, if `t ≡ 1 [ZMOD 5]` or `t ≡ 3 [ZMOD 5]`, substituting these values into `t^2 + t + 3` yields `0 [ZMOD 5]`.
-/

@[autogradedProof 3]
theorem problem2 : ¬ (∃ x : ℝ, ∀ y : ℝ, y ≤ x) := by
  intro h
  obtain ⟨x, hx⟩ := h
  have hx' := hx (x + 1)
  addarith [hx']

/-
**Human-readable proof:**

Assume, for contradiction, that there exists a real number `x` such that for every real number `y`, `y ≤ x`.
Consider the real number `x + 1`. By our assumption, `x + 1 ≤ x`.
Subtracting `x` from both sides gives `1 ≤ 0`, which is a contradiction since `1` is greater than `0`.
Therefore, no such `x` exists.
-/

@[autogradedProof 3]
theorem problem3 (a : ℚ) : 3 * a + 2 < 11 ↔ a < 3 := by
  constructor
  · intro h
    calc a = (3 * a + 2 - 2) / 3 := by ring
      _ < (11 - 2) / 3 := by rel [h]
      _ = 3 := by numbers
  · intro h
    calc 3 * a + 2 < 3 * 3 + 2 := by rel [h]
      _ = 11 := by numbers

@[autogradedProof 4]
theorem problem5 (P Q : Prop) : (P ∧ Q) ↔ (Q ∧ P) := by
  constructor
  · intro h
    obtain ⟨hp, hq⟩ := h
    exact ⟨hq, hp⟩
  · intro h
    obtain ⟨hq, hp⟩ := h
    exact ⟨hp, hq⟩

@[autogradedProof 5]
theorem problem6 (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  constructor
  · intro h
    obtain ⟨⟨x, hx⟩, hq⟩ := h
    exact ⟨x, ⟨hx, hq⟩⟩
  · intro h
    obtain ⟨x, ⟨hx, hq⟩⟩ := h
    exact ⟨⟨x, hx⟩, hq⟩
