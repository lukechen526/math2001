/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Theory.ParityModular
import Library.Basic
import Library.Tactic.ModEq

math2001_init

open Int


example : ¬ (∀ x : ℝ, x ^ 2 ≥ x) := by
  intro h
  have : 0.5 ^ 2 ≥ 0.5 := h 0.5
  numbers at this


example : ¬ 3 ∣ 13 := by
  intro H
  obtain ⟨k, hk⟩ := H
  obtain h4 | h5 := le_or_succ_le k 4
  · have h :=
    calc 13 = 3 * k := hk
      _ ≤ 3 * 4 := by rel [h4]
    numbers at h
  · have h :=
    calc 13 = 3 * k := hk
      _ ≥ 3 * 5 := by rel [h5]
    numbers at h

example {x y : ℝ} (h : x + y = 0) : ¬(x > 0 ∧ y > 0) := by
  intro h
  obtain ⟨hx, hy⟩ := h
  have H :=
  calc 0 = x + y := by rw [h]
    _ > 0 := by extra
  numbers at H


example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  intro h
  obtain ⟨n, hn⟩ := h
  obtain h1 | h2 := le_or_succ_le n 1
  · have h :=
    calc 2 = n ^ 2 := by rw [hn]
      _ ≤ 1 ^ 2 := by rel [h1]
    numbers at h
  · have h :=
    calc 2 = n ^ 2 := by rw [hn]
      _ ≥ 2 ^ 2 := by rel [h2]
    numbers at h

example (n : ℤ) : Int.Even n ↔ ¬ Int.Odd n := by
  constructor
  · intro h1 h2
    rw [Int.even_iff_modEq] at h1
    rw [Int.odd_iff_modEq] at h2
    have h :=
    calc 0 ≡ n [ZMOD 2] := by rel [h1]
      _ ≡ 1 [ZMOD 2] := by rel [h2]
    numbers at h -- contradiction!
  · intro h
    obtain h1 | h2 := Int.even_or_odd n
    · apply h1
    · contradiction


example (n : ℤ) : Int.Odd n ↔ ¬ Int.Even n := by
  constructor
  · intro h1 h2
    rw [Int.odd_iff_modEq] at h1
    rw [Int.even_iff_modEq] at h2
    have h :=
    calc 1 ≡ n [ZMOD 2] := by rel [h1]
      _ ≡ 0 [ZMOD 2] := by rel [h2]
    numbers at h -- contradiction!
  · intro h
    obtain h1 | h2 := Int.even_or_odd n
    · contradiction
    · apply h2


example (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 3]) := by
  intro h
  mod_cases hn : n % 3
  · have h' :=
    calc (0:ℤ) = 0 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h' -- contradiction!
  · have h' :=
    calc (1:ℤ) = 1 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h' -- contradiction!
  · have h' :=
    calc (1: ℤ) ≡ 1 + 3 * 1 [ZMOD 3] := by extra
      _ = 4 := by ring
      _ = 2 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h' -- contradiction!

example {p : ℕ} (k l : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hkl : p = k * l) :
    ¬(Prime p) := by
  have hk : k ∣ p
  · use l
    apply hkl
  intro h
  obtain ⟨h2, hfact⟩ := h
  have : k = 1 ∨ k = p := hfact k hk
  obtain hk1' | hkp' := this
  · contradiction
  · contradiction


example (a b : ℤ) (h : ∃ q, b * q < a ∧ a < b * (q + 1)) : ¬b ∣ a := by
  intro H
  obtain ⟨k, hk⟩ := H
  obtain ⟨q, hq₁, hq₂⟩ := h
  have hb :=
    calc 0 = a - a := by ring
      _ < b * (q + 1) - b * q := by rel [hq₁, hq₂]
      _ = b := by ring
  have h1 :=
    calc b * k = a := by rw [hk]
      _ < b * (q + 1) := hq₂
  cancel b at h1
  sorry

example {p : ℕ} (hp : 2 ≤ p)  (T : ℕ) (hTp : p < T ^ 2)
    (H : ∀ (m : ℕ), 1 < m → m < T → ¬ (m ∣ p)) :
    Prime p := by
  apply prime_test hp
  intro m hm1 hmp
  obtain hmT | hmT := lt_or_le m T
  · apply H m hm1 hmT
  intro h_div
  obtain ⟨l, hl⟩ := h_div
  have : l ∣ p
  · use m
    rw [mul_comm, hl]
  have hl1 :=
    calc m * 1 = m := by ring
      _ < p := hmp
      _ = m * l := hl
  cancel m at hl1
  have hl2 : l < T
  ·
    have h' := Nat.lt_or_ge l T
    obtain h | h := h'
    · exact h
    · have h'' :=
       calc p = m * l := hl
            _ ≥ T * T := by rel [h, hmT]
            _ = T ^ 2 := by ring

      have h''' := not_lt_of_ge h''
      contradiction

  have : ¬ l ∣ p := H l hl1 hl2
  contradiction


example : Prime 79 := by
  apply better_prime_test (T := 9)
  · numbers
  · numbers
  intro m hm1 hm2
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 39
    constructor <;> numbers
  · use 26
    constructor <;> numbers
  · use 19
    constructor <;> numbers
  · use 15
    constructor <;> numbers
  · use 13
    constructor <;> numbers
  · use 11
    constructor <;> numbers
  · use 9
    constructor <;> numbers

/-! # Exercises -/


example : ¬ (∃ t : ℝ, t ≤ 4 ∧ t ≥ 5) := by
  intro h
  obtain ⟨s, t, u⟩ := h
  have :=
    calc s ≤ 4 := t
      _ < 5 := by numbers
  apply not_lt_of_ge u
  exact this

example : ¬ (∃ a : ℝ, a ^ 2 ≤ 8 ∧ a ^ 3 ≥ 30) := by
  intro H
  obtain ⟨a, ha₁ , ha₂⟩ := H
  have h1 :=
  calc
    a ^ 6 = (a ^ 2) ^ 3 := by ring
      _ = (a ^ 2) * (a ^ 2) * (a ^ 2) := by ring
      _ ≤ 8 * 8 * 8 := by rel [ha₁]
      _= 512 := by numbers
  have h2 :=
  calc
    a ^ 6 = (a ^ 3) ^ 2 := by ring
      _ ≥ 30 ^ 2 := by rel [ha₂]
      _ = 900 := by numbers
      _ > 512 := by numbers

  apply not_lt_of_ge h1
  exact h2

example : ¬ Int.Even 7 := by
  intro H
  rw [Int.even_iff_modEq] at H
  have H1 :=
  calc
    1 ≡ 1 + 2 * 3 [ZMOD 2] := by extra
     _ ≡ 7 [ZMOD 2] := by numbers
     _ ≡ 0 [ZMOD 2] := by rel [H]
  numbers at H1

example {n : ℤ} (hn : n + 3 = 7) : ¬ (Int.Even n ∧ n ^ 2 = 10) := by
  intro H
  obtain ⟨h1, h2⟩ := H
  have h3 :=
  calc
    n = (n + 3) - 3 := by ring
      _ = 7 - 3 := by rw [hn]
      _ = 4 := by numbers
  have h4 :=
  calc
    n ^ 2 = 4 ^ 2 := by rw [h3]
      _ = 16 := by numbers
      _ ≠ 10 := by numbers
  contradiction

example {x : ℝ} (hx : x ^ 2 < 9) : ¬ (x ≤ -3 ∨ x ≥ 3) := by
  intro H
  obtain h1 | h2 := H
  · have h3₁ : -x ≥ 3 :=  by addarith [h1]
    have h3₂ :=
      calc
        x ^ 2 = (-x) ^ 2 := by ring
          _ ≥ 3 ^ 2 := by rel [h3₁]
          _ = 9 := by numbers
    apply not_lt_of_ge h3₂
    exact hx

  · have h4 :=
      calc
      x ^ 2 = x * x := by ring
        _ ≥ 3 * 3 := by rel [h2]
        _ = 9 := by numbers
    apply not_lt_of_ge h4
    exact hx

example : ¬ (∃ N : ℕ, ∀ k > N, Nat.Even k) := by
  intro H
  obtain ⟨n, hN⟩ := H
  obtain h1 | h2 := Nat.even_or_odd n
  · have h3: Nat.Even (n + 1) := by
      apply hN (n + 1)
      extra
    obtain ⟨k, hk⟩ := h1
    rw [Nat.even_iff_not_odd] at h3
    have h4 : Nat.Odd (n + 1) := by
      dsimp [Nat.Odd]
      use k
      calc
        n + 1 = (n) + 1 := by ring
          _ = 2 * k + 1 := by rw [hk]
    contradiction

  · have h3: Nat.Even (n + 2) := by
      apply hN (n + 2)
      extra
    obtain ⟨k, hk⟩ := h2
    rw [Nat.even_iff_not_odd] at h3
    have h4 : Nat.Odd (n + 2) := by
      dsimp [Nat.Odd]
      use k + 1
      calc
        n + 2 = (n) + 2:= by ring
          _ = (2 * k + 1) + 2 := by rw [hk]
          _ = 2 * (k + 1) + 1 := by ring
    contradiction


example (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 4]) := by
  intro H
  mod_cases hn : n % 4
  · have h1 :=
    calc 0 ≡ 0 ^ 2 [ZMOD 4] := by numbers
      _ ≡ n ^ 2 [ZMOD 4] := by rel [hn]
      _ ≡ 2 [ZMOD 4] := by rel [H]
    numbers at h1
  · have h1 :=
    calc 1 ≡ 1 ^ 2 [ZMOD 4] := by numbers
      _ ≡ n ^ 2 [ZMOD 4] := by rel [hn]
      _ ≡ 2 [ZMOD 4] := by rel [H]
    numbers at h1
  · have h1 :=
    calc 0 ≡ 0 + 1 * 4 [ZMOD 4] := by extra
      _ = 4 := by ring
      _ = 2 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 4] := by rel [hn]
      _ ≡ 2 [ZMOD 4] := by rel [H]
    numbers at h1
  · have h1 :=
    calc 1 ≡ 1 + 2 * 4 [ZMOD 4] := by extra
      _ = 9 := by ring
      _ = 3 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 4] := by rel [hn]
      _ ≡ 2 [ZMOD 4] := by rel [H]
    numbers at h1


example : ¬ Prime 1 := by
  intro H
  obtain ⟨h1, h2⟩ := H
  numbers at h1


example : Prime 97 := by
  sorry
