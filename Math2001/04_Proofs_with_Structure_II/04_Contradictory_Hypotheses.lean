/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init


example {y : ℝ} (x : ℝ) (h : 0 < x * y) (hx : 0 ≤ x) : 0 < y := by
  obtain hneg | hpos : y ≤ 0 ∨ 0 < y := le_or_lt y 0
  · -- the case `y ≤ 0`
    have : ¬0 < x * y
    · apply not_lt_of_ge
      calc
        0 = x * 0 := by ring
        _ ≥ x * y := by rel [hneg]
    contradiction
  · -- the case `0 < y`
    apply hpos


example {t : ℤ} (h2 : t < 3) (h : t - 1 = 6) : t = 13 := by
  have H :=
  calc
    7 = t := by addarith [h]
    _ < 3 := h2
  have : ¬(7 : ℤ) < 3 := by numbers
  contradiction


example {t : ℤ} (h2 : t < 3) (h : t - 1 = 6) : t = 13 := by
  have H :=
  calc
    7 = t := by addarith [h]
    _ < 3 := h2
  numbers at H -- this is a contradiction!


example (n : ℤ) (hn : n ^ 2 + n + 1 ≡ 1 [ZMOD 3]) :
    n ≡ 0 [ZMOD 3] ∨ n ≡ 2 [ZMOD 3] := by
  mod_cases h : n % 3
  · -- case 1: `n ≡ 0 [ZMOD 3]`
    left
    apply h
  · -- case 2: `n ≡ 1 [ZMOD 3]`
    have H :=
      calc 0 ≡ 0 + 3 * 1 [ZMOD 3] := by extra
      _ = 1 ^ 2 + 1 + 1 := by numbers
      _ ≡ n ^ 2 + n + 1 [ZMOD 3] := by rel [h]
      _ ≡ 1 [ZMOD 3] := hn
    numbers at H -- contradiction!
  · -- case 3: `n ≡ 2 [ZMOD 3]`
    right
    apply h


example {p : ℕ} (hp : 2 ≤ p) (H : ∀ m : ℕ, 1 < m → m < p → ¬m ∣ p) : Prime p := by
  constructor
  · apply hp -- show that `2 ≤ p`
  intro m hmp
  have hp' : 0 < p := by extra
  have h1m : 1 ≤ m := Nat.pos_of_dvd_of_pos hmp hp'
  obtain hm | hm_left : 1 = m ∨ 1 < m := eq_or_lt_of_le h1m
  · -- the case `m = 1`
    left
    addarith [hm]
  -- the case `1 < m`
  · right
    have hmp' : m ≤ p := Nat.le_of_dvd hp' hmp
    obtain hm | hm_right : m = p ∨ m < p := eq_or_lt_of_le hmp'
    · -- the case `m = p`
      exact hm
    · -- the case `m < p`
      have : ¬m ∣ p := H m hm_left hm_right
      contradiction

example : Prime 5 := by
  apply prime_test
  · numbers
  intro m hm_left hm_right
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 2
    -- <;> connects two tactics, performing the second one on every goal created by the first one.
    constructor <;> numbers
  · use 1
    constructor <;> numbers
  · use 1
    constructor <;> numbers


example {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h_pyth : a ^ 2 + b ^ 2 = c ^ 2) : 3 ≤ a := by
    have hn :=  le_or_succ_le a 2
    obtain h_le | h_succ_le := hn
    -- the case a ≤  2
    · have hn1 :=  le_or_succ_le b 1


    -- the case 3 ≤ a
    . exact h_succ_le



/-! # Exercises -/


example {x y : ℝ} (n : ℕ) (hx : 0 ≤ x) (hn : 0 < n) (h : y ^ n ≤ x ^ n) :
    y ≤ x := by
  obtain hneg | hpos : y ≤ x ∨ x < y := le_or_lt y x
  · -- the case `y ≤ x`
    exact hneg
  · -- the case `x < y`
    have h' := pow_lt_pow_of_lt_left hpos hx hn
    have h'' := not_le_of_lt h'
    contradiction

example (n : ℤ) (hn : n ^ 2 ≡ 4 [ZMOD 5]) : n ≡ 2 [ZMOD 5] ∨ n ≡ 3 [ZMOD 5] := by
  mod_cases h : n % 5
  · -- case 1: `n ≡ 0 [ZMOD 5]`
    have H :=
      calc 0 ≡ 0 [ZMOD 5] := by extra
      _ ≡ 0 ^ 2 [ZMOD 5]:= by numbers
      _ ≡ n ^ 2 [ZMOD 5] := by rel [h]
      _ ≡ 4 [ZMOD 5] := hn
    numbers at H -- contradiction!
  · -- case 2: `n ≡ 1 [ZMOD 5]`
    have H :=
      calc 1 ≡ 1 [ZMOD 5] := by extra
      _ ≡ 1 ^ 2 [ZMOD 5]:= by numbers
      _ ≡ n ^ 2 [ZMOD 5] := by rel [h]
      _ ≡ 4 [ZMOD 5] := hn
    numbers at H -- contradiction!
  · -- case 3: `n ≡ 2 [ZMOD 5]`
    left
    apply h
  · -- case 4: `n ≡ 3 [ZMOD 5]`
    right
    apply h
  · -- case 5: `n ≡ 4 [ZMOD 5]`
    have H :=
      calc 1 ≡ 1 + 5 * 3 [ZMOD 5] := by extra
      _ ≡ 16 [ZMOD 5]:= by numbers
      _ ≡ 4 ^ 2 [ZMOD 5]:= by numbers
      _ ≡ n ^ 2 [ZMOD 5] := by rel [h]
      _ ≡ 4 [ZMOD 5] := hn
    numbers at H -- contradiction!

example : Prime 7 := by
  apply prime_test
  · numbers
  intro m hm_left hm_right
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 3
    constructor <;> numbers
  · use 2
    constructor <;> numbers
  · use 1
    constructor <;> numbers
  · use 1
    constructor <;> numbers
  · use 1
    constructor <;> numbers


example {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 := by
  have h3 :=
    calc
      (x + 2) * (x - 2) = x ^ 2 + 2 * x - 2 * x - 4 := by ring
      _ = 0 := by addarith [h1]
  rw [mul_eq_zero] at h3
  sorry

namespace Nat

example (p : ℕ) (h : Prime p) : p = 2 ∨ Odd p := by
  dsimp [Prime] at h
  obtain ⟨h2, h3⟩ := h
  have h' := Nat.eq_or_lt_of_le h2
  obtain h4 | h5 := h'
  left -- the case `p = 2`
  · addarith [h4]
  right -- the case `Odd p`
  obtain h6 | h7 := Nat.even_or_odd p
  · -- the case `Even p`
    obtain ⟨k, hk⟩ := h6
    have h8  : k ∣ p :=  by rw [hk]; apply dvd_mul_left
    have h9 : 2 * k > 2 * 1 := by
      calc
        2 * k = p := by rw [hk]
           _ > 2 := by rel [h5]
           _ = 2 * 1 := by ring
    cancel 2 at h9
    have h10: p > k := by
      calc
        p = 2 * k := by rw [hk]
        _ = k + k := by ring
        _ > k + 1 := by rel [h9]
        _ > k := by extra

    have h11 := ne_of_gt h9
    have h12 := ne_of_gt h10
    obtain h13 | h14 := h3 k h8
    contradiction

  · -- the case `Odd p`
    exact h7
