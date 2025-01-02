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

@[autogradedProofProof 4]
theorem problem1 : ¬ (∃ t : ℝ, t ≤ 5 ∧ 2 * t ≥ 12) := by
  intro H
  obtain ⟨t, ht1, ht2⟩ := H
  have ht3 :=
  calc 12 ≤ 2 * t := ht2
    _ ≤ 2 * 5 := by rel [ht1]
    _ = 10 := by numbers
  numbers at ht3

@[autogradedProofProof 3]
theorem problem2 : ¬ (∃ x : ℝ, ∀ y : ℝ, y ≤ x) := by
  sorry

@[autogradedProofProof 3]
theorem problem3 (a : ℚ) : 3 * a + 2 < 11 ↔ a < 3 := by
  sorry

@[autogradedProofProof 6]
theorem problem4 (t : ℤ) : t ^ 2 + t + 3 ≡ 0 [ZMOD 5] ↔ t ≡ 1 [ZMOD 5] ∨ t ≡ 3 [ZMOD 5] := by
  sorry

@[autogradedProofProof 4]
theorem problem5 (P Q : Prop) : (P ∧ Q) ↔ (Q ∧ P) := by
  sorry

@[autogradedProofProof 5]
theorem problem6 (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  sorry
