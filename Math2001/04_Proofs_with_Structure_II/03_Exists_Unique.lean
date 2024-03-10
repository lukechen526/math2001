/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Theory.ModEq.Defs

math2001_init

namespace Int


example : ∃! a : ℝ, 3 * a + 1 = 7 := by
  use 2
  dsimp
  constructor
  · numbers
  intro y hy
  calc
    y = (3 * y + 1 - 1) / 3 := by ring
    _ = (7 - 1) / 3 := by rw [hy]
    _ = 2 := by numbers


example : ∃! x : ℚ, ∀ a, a ≥ 1 → a ≤ 3 → (a - x) ^ 2 ≤ 1 := by
  use 2
  dsimp
  constructor
  · intro a ha1 ha2
    have ha1' : -1 ≤ a - 2 := by addarith [ha1]
    have ha2' : 1 ≥ a - 2 := by addarith [ha2]
    have ha3 : (a - 2) ^ 2 ≤ 1 ^ 2 := by apply sq_le_sq' ha1' ha2'
    calc
      (a - 2) ^ 2 ≤ 1 ^ 2 := ha3
      _ = 1 := by ring
  · intro y hy
    have h1 : (1 - y) ^ 2 ≤ 1 := by
      apply hy 1
      numbers
    have h2 : (3 - y) ^ 2 ≤ 1 := by
      apply hy 3
      numbers
    have h3 : (y - 2) ^ 2 = 0 := by
      apply le_antisymm
      · calc
          (y - 2) ^ 2 = ((1 - y) ^ 2 + (3 - y) ^ 2 - 2 ) / 2:= by ring
                    _ ≤ (1 + 1 - 2) / 2 := by rel [h1, h2]
                    _ = 0 := by ring
      · apply sq_nonneg
    have h4 : y - 2 = 0 := by
      have : (y - 2)  * (y - 2) = 0 := by
        calc
          (y - 2) * (y - 2) = (y - 2) ^ 2 := by ring
          _ = 0 := by rw [h3]
      apply eq_zero_of_mul_self_eq_zero this
    addarith [h4]


example {x : ℚ} (hx : ∃! a : ℚ, a ^ 2 = x) : x = 0 := by
  obtain ⟨a, ha1, ha2⟩ := hx
  have h1 : -a = a
  · apply ha2
    calc
      (-a) ^ 2 = a ^ 2 := by ring
      _ = x := ha1
  have h2 :=
    calc
      a = (a - -a) / 2 := by ring
      _ = (a - a) / 2 := by rw [h1]
      _ = 0 := by ring
  calc
    x = a ^ 2 := by rw [ha1]
    _ = 0 ^ 2 := by rw [h2]
    _ = 0 := by ring


example : ∃! r : ℤ, 0 ≤ r ∧ r < 5 ∧ 14 ≡ r [ZMOD 5] := by
  use 4
  dsimp
  constructor
  · constructor
    · numbers
    constructor
    · numbers
    use 2
    numbers
  intro r hr
  obtain ⟨hr1, hr2, q, hr3⟩ := hr
  have :=
    calc
      5 * 1 < 14 - r := by addarith [hr2]
      _ = 5 * q := by rw [hr3]
  cancel 5 at this
  have :=
    calc
      5 * q = 14 - r := by rw [hr3]
      _ < 5 * 3 := by addarith [hr1]
  cancel 5 at this
  interval_cases q
  addarith [hr3]

/-! # Exercises -/


example : ∃! x : ℚ, 4 * x - 3 = 9 := by
  use 3
  dsimp
  constructor
  · numbers
  intro y hy
  calc
    y = (4 * y - 3 + 3) / 4 := by ring
    _ = (9 + 3) / 4 := by rw [hy]
    _ = 3 := by numbers

example : ∃! n : ℕ, ∀ a, n ≤ a := by
  use 0
  dsimp
  constructor
  · intro a
    apply Nat.zero_le
  intro m hm
  have h1 : 0 ≤ m := by apply Nat.zero_le
  have h2 : m ≤ 0 := by apply hm
  exact le_antisymm h2 h1

example : ∃! r : ℤ, 0 ≤ r ∧ r < 3 ∧ 11 ≡ r [ZMOD 3] := by
  use 2
  dsimp
  constructor
  · constructor
    · numbers
    constructor
    · numbers
    use 3
    numbers
  intro r hr
  obtain ⟨hr1, hr2, q, hr3⟩ := hr
  have :=
    calc
      3 * 2 < 11 - r := by addarith [hr2]
      _ = 3 * q := by rw [hr3]
  cancel 3 at this
  have :=
    calc
      3 * q = 11 - r := by rw [hr3]
      _ < 3 * 4 := by addarith [hr1]
  cancel 3 at this
  interval_cases q
  addarith [hr3]
