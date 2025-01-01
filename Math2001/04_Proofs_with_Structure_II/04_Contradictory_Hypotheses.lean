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
  obtain hn | hn := h3
  · -- case `x + 2 = 0`
    have :=
      calc
        -2 = 0 - 2 := by ring
        _ = x := by addarith [hn]
        _ > 1 := by addarith [h2]

    numbers at this
  · addarith [hn]

namespace Nat

example (p : ℕ) (h : Prime p) : p = 2 ∨ Odd p := by
  -- Unfold the definition of `Prime` to access its components
  dsimp [Prime] at h
  -- Extract the two parts of the `Prime` definition:
  -- `h2` states that `2 ≤ p`, and `h3` states that `p` has no divisors other than 1 and itself.
  obtain ⟨h2, h3⟩ := h

  -- Consider whether `p = 2` or `p > 2`
  obtain h4 | h5 := Nat.eq_or_lt_of_le h2

  · -- Case 1: `p = 2`
    left
    addarith [h4]
  · -- Case 2: `p > 2`
    -- consider whether `p` is even or odd
    have h6 := Nat.even_or_odd p
    obtain h7 | h8 := h6
    · -- Case 2a: `p` is even
      -- Since `p` is even, we can write `p` as `2 * k` for some natural number `k`
      rw [Even] at h7
      obtain ⟨k, hk⟩ := h7
      -- Show that `2` divides `p` using the fact that `p = 2 * k`
      have h9 : 2 ∣ p :=
        by use k; rw [hk]
      -- Since `p` is prime and `2` divides `p`, by the definition of `Prime`, `2` must be either `1` or `p`
      obtain h10 | h11 := h3 2 h9
      · -- Subcase 2a1: `2 = 1`
        -- This is a contradiction since `2` is not equal to `1`
        numbers at h10
      · -- Subcase 2a2: `2 = p`
        -- This implies `p = 2`, but we are in the case where `p > 2`, leading to a contradiction
        have :=
        calc 2 = p := h11
         _ > 2 := h5
        numbers at this
    · -- Case 2b: `p` is odd
      -- Since `p` is odd, we can directly conclude that `p` is odd by using the hypothesis `h8`
      right
      exact h8
