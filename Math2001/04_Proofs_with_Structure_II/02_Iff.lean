/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init

namespace Int


example {a : ℚ} : 3 * a + 1 ≤ 7 ↔ a ≤ 2 := by
  constructor
  · intro h
    calc a = ((3 * a + 1) - 1) / 3 := by ring
      _ ≤ (7 - 1) / 3 := by rel [h]
      _ = 2 := by numbers
  · intro h
    calc 3 * a + 1 ≤ 3 * 2 + 1 := by rel [h]
      _ = 7 := by numbers


example {n : ℤ} : 8 ∣ 5 * n ↔ 8 ∣ n := by
  constructor
  · intro hn
    obtain ⟨a, ha⟩ := hn
    use -3 * a + 2 * n
    calc
      n = -3 * (5 * n) + 16 * n := by ring
      _ = -3 * (8 * a) + 16 * n := by rw [ha]
      _ = 8 * (-3 * a + 2 * n) := by ring
  · intro hn
    obtain ⟨a, ha⟩ := hn
    use 5 * a
    calc 5 * n = 5 * (8 * a) := by rw [ha]
      _ = 8 * (5 * a) := by ring


theorem odd_iff_modEq (n : ℤ) : Odd n ↔ n ≡ 1 [ZMOD 2] := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    dsimp [Int.ModEq]
    dsimp [(· ∣ ·)]
    use k
    addarith [hk]
  · intro ha
    dsimp [Int.ModEq] at ha
    dsimp [(· ∣ ·)] at ha
    obtain ⟨k, hk⟩ := ha
    dsimp [Int.Odd]
    use k
    addarith [hk]

theorem even_iff_modEq (n : ℤ) : Even n ↔ n ≡ 0 [ZMOD 2] := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    calc
      n = 2 * k := by rw [hk]
      _ = 0 + 2 * k := by ring
      _ ≡ 0 [ZMOD 2] := by extra
  · intro h
    dsimp [Even]
    dsimp [Int.ModEq] at h
    dsimp [(· ∣ ·)] at h
    obtain ⟨a, ha⟩ := h
    use a
    addarith [ha]

example {x : ℝ} : x ^ 2 + x - 6 = 0 ↔ x = -3 ∨ x = 2 := by
  constructor
  -- `x ^ 2 + x - 6 = 0 → x = -3 ∨ x = 2`
  · intro h
    have h1 : (x + 3) * (x - 2) = 0 := by
      calc
        (x + 3) * (x - 2) = x ^ 2 - 2 * x + 3 * x - 6 := by ring
                        _ = x ^ 2 + x - 6 := by ring
                        _ = 0 := by rel [h]
    have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
    obtain h3 | h4 := h2
    · left
      addarith [h3]
    · right
      addarith [h4]
   -- `x = -3 ∨ x = 2 → x ^ 2 + x - 6 = 0`
  · intro h
    obtain h1 | h2 := h
    · rw [h1]
      ring
    · rw [h2]
      ring

example {a : ℤ} : a ^ 2 - 5 * a + 5 ≤ -1 ↔ a = 2 ∨ a = 3 := by
  constructor
  -- `a ^ 2 - 5 * a + 5 ≤ -1 → a = 2 ∨ a = 3`
  · intro h
    have h1: (2 * a - 5) ^ 2 ≤ 1 ^ 2 := by
      calc
        (2 * a - 5) ^ 2 = 4 * (a ^ 2 - 5 * a + 5) + 5 := by ring
                      _ ≤ 4 * (-1) + 5 := by rel [h]
                      _ = 1 := by ring
                      _ = 1 ^ 2 := by ring
    have h2: -1 ≤ 2 * a - 5 ∧ 2 * a - 5 ≤ 1:= by
      apply abs_le_of_sq_le_sq'
      exact h1
      numbers
    obtain ⟨h3, h4⟩ := h2
    have h3': 2 * 2 ≤ 2 * a := by addarith [h3]
    have h3'': 2 ≤ a := by cancel 2 at h3'
    have h4': 2 * a ≤ 2 * 3 := by addarith [h4]
    have h4'': a ≤ 3 := by cancel 2 at h4'

    interval_cases a
    · left
      numbers
    · right
      numbers
  -- `a = 2 ∨ a = 3 → a ^ 2 - 5 * a + 5 ≤ -1`
  · intro h
    obtain h1 | h2 := h
    · calc
      a ^ 2 - 5 * a + 5 = 2 ^ 2 - 5 * 2 + 5 := by rw [h1]
                      _ = -1 := by ring
      numbers
    · calc
      a ^ 2 - 5 * a + 5 = 3 ^ 2 - 5 * 3 + 5 := by rw [h2]
                      _ = -1 := by ring
      numbers

example {n : ℤ} (hn : n ^ 2 - 10 * n + 24 = 0) : Even n := by
  have hn1 :=
    calc (n - 4) * (n - 6) = n ^ 2 - 10 * n + 24 := by ring
      _ = 0 := hn
  have hn2 := eq_zero_or_eq_zero_of_mul_eq_zero hn1
  obtain hn | hn := hn2
  · use 2
    addarith [hn]
  · use 3
    addarith [hn]

example {n : ℤ} (hn : n ^ 2 - 10 * n + 24 = 0) : Even n := by
  have hn1 :=
    calc (n - 4) * (n - 6) = n ^ 2 - 10 * n + 24 := by ring
      _ = 0 := hn
  rw [mul_eq_zero] at hn1 -- `hn1 : n - 4 = 0 ∨ n - 6 = 0`
  obtain h4 | h6 := hn1
  ·
    use 2
    addarith [h4]
  ·
    use 3
    addarith [h6]

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x + y + 1) := by
  rw [Int.odd_iff_modEq] at *
  calc x + y + 1 ≡ 1 + 1 + 1 [ZMOD 2] := by rel [hx, hy]
    _ = 2 * 1 + 1 := by ring
    _ ≡ 1 [ZMOD 2] := by extra


example (n : ℤ) : Even n ∨ Odd n := by
  mod_cases hn : n % 2
  · left
    rw [Int.even_iff_modEq]
    apply hn
  · right
    rw [Int.odd_iff_modEq]
    apply hn

/-! # Exercises -/


example {x : ℝ} : 2 * x - 1 = 11 ↔ x = 6 := by
  constructor
  · intro h1
    calc
      x = (2 * x - 1 + 1) / 2 := by ring
      _ = (11 + 1) / 2 := by rw [h1]
      _ = 6 := by ring
  · intro h2
    calc
      2 * x - 1 = 2 * 6 - 1 := by rw [h2]
            _ = 11 := by ring

example {n : ℤ} : 63 ∣ n ↔ 7 ∣ n ∧ 9 ∣ n := by
  constructor
  · intro h1
    obtain ⟨a, ha⟩ := h1
    constructor
    · use 9 * a
      calc
        n = 63 * a := by rw [ha]
          _ = 7 * 9 * a := by ring
          _ = 7 * (9 * a) := by ring
    · use 7 * a
      calc
        n = 63 * a := by rw [ha]
          _ = 9 * 7 * a := by ring
          _ = 9 * (7 * a) := by ring
  · intro h2
    obtain ⟨h7, h8⟩ := h2
    obtain ⟨a, ha⟩ := h7
    obtain ⟨b, hb⟩ := h8
    use 4 * a - 5 * b
    calc
      n = 36 * n - 35 * n := by ring
        _ = 36 * (7 * a) - 35 * (9 * b) := by nth_rewrite 1 [ha]; nth_rewrite 1 [hb]; ring
        _ = 63 * (4 * a - 5 * b) := by ring


theorem dvd_iff_modEq {a n : ℤ} : n ∣ a ↔ a ≡ 0 [ZMOD n] := by
  dsimp [(· ∣ ·), Int.ModEq] at *
  constructor
  · intro h1
    obtain ⟨k, hk⟩ := h1
    use k
    addarith [hk]
  · intro h2
    obtain ⟨k, hk⟩ := h2
    use k
    addarith [hk]

example {a b : ℤ} (hab : a ∣ b) : a ∣ 2 * b ^ 3 - b ^ 2 + 3 * b := by
  rw [Int.dvd_iff_modEq] at *
  calc
    2 * b ^ 3 - b ^ 2 + 3 * b ≡ 2 * 0 ^ 3 - 0 ^ 2 + 3 * 0 [ZMOD a] := by rel [hab]
                            _ = 0 := by ring

example {k : ℕ} : k ^ 2 ≤ 6 ↔ k = 0 ∨ k = 1 ∨ k = 2 := by
  constructor
  · intro h1
    -- Prove that k ^ 2 < 9 implies k < 3
    have h2 : k < 3
    · apply lt_of_pow_lt_pow 2
      · numbers
      · calc
          k ^ 2 ≤ 6 := h1
          _ < 9 := by numbers
    interval_cases k
    · left
      rfl
    · right
      left
      rfl
    · right
      right
      rfl
  · intro h2
    obtain h3 | h4 | h5 := h2
    · rw [h3]
      numbers
    · rw [h4]
      numbers
    · rw [h5]
      numbers
