/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Tactic.GCongr
import Library.Basic
import AutograderLib

math2001_init

/-! # Homework 0

Don't forget to compare with the text version
for clearer statements and any special instructions. -/


@[autogradedProofProof 5]
theorem problem1 {n : ℤ} (hn : n ≥ 5) : n ^ 2 > 2 * n + 11 :=
  calc
    n ^ 2 = n * n := by ring
    _ ≥ 5 * n := by rel [hn]
    _ = 2 * n + 3 * n := by ring
    _ ≥ 2 * n + 3 * 5 := by rel [hn]
    _ = 2 * n + 15 := by ring
    _ = 2 * n + 11 + 4 := by ring
    _ > 2 * n + 11 := by extra
