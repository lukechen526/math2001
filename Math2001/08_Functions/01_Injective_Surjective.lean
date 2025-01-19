/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Exhaust
import Library.Tactic.ModEq
import Library.Theory.ParityModular

math2001_init
set_option pp.funBinderTypes true

open Function
namespace Int


def F : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 => F (n + 1) + F n

#eval F 5 -- infoview displays `8`


#check @F -- infoview displays `F : ℕ → ℤ`


def q (x : ℝ) : ℝ := x + 3


#check @q -- infoview displays `q : ℝ → ℝ`


#check fun (x : ℝ) ↦ x ^ 2 -- infoview displays `fun x ↦ x ^ 2 : ℝ → ℝ`


example : Injective q := by
  dsimp [Injective]
  intro x1 x2 h
  dsimp [q] at h
  addarith [h]


example : ¬ Injective (fun x : ℝ ↦ x ^ 2) := by
  dsimp [Injective]
  push_neg
  use -1, 1
  constructor
  · numbers
  · numbers


def s (a : ℚ) : ℚ := 3 * a + 2

example : Surjective s := by
  dsimp [Surjective]
  intro y
  use (y - 2) / 3
  calc s ((y - 2) / 3) = 3 * ((y - 2) / 3) + 2 := by rw [s]
    _ = y := by ring


example : ¬ Surjective (fun x : ℝ ↦ x ^ 2) := by
  dsimp [Surjective]
  push_neg
  use -1
  intro x
  apply ne_of_gt
  calc -1 < 0 := by numbers
    _ ≤ x ^ 2 := by extra


inductive Musketeer
  | athos
  | porthos
  | aramis
  deriving DecidableEq

open Musketeer


def f : Musketeer → Musketeer
  | athos => aramis
  | porthos => aramis
  | aramis => athos


example : ¬ Injective f := by
  dsimp [Injective]
  push_neg
  use athos, porthos
  dsimp [f] -- optional
  exhaust


example : ¬ Surjective f := by
  dsimp [Surjective]
  push_neg
  use porthos
  intro a
  cases a
  · exhaust
  · exhaust
  · exhaust


-- better (more automated) version of the previous proof
example : ¬ Surjective f := by
  dsimp [Surjective]
  push_neg
  use porthos
  intro a
  cases a <;> exhaust


def g : Musketeer → Musketeer
  | athos => porthos
  | porthos => aramis
  | aramis => athos


example : Injective g := by
  dsimp [Injective]
  intro x1 x2 hx
  cases x1 <;> cases x2 <;> exhaust


example : Surjective g := by
  dsimp [Surjective]
  intro y
  cases y
  · use aramis
    exhaust
  · use athos
    exhaust
  · use porthos
    exhaust



example : Injective (fun (x:ℝ) ↦ x ^ 3) := by
  intro x1 x2 hx
  dsimp at hx
  have H : (x1 - x2) * (x1 ^ 2 + x1 * x2 + x2 ^ 2) = 0
  · calc (x1 - x2) * (x1 ^ 2 + x1 * x2 + x2 ^ 2) = x1 ^ 3 - x2 ^ 3 := by ring
      _ = x1 ^ 3 - x1 ^ 3 := by rw [hx]
      _ = 0 := by ring
  rw [mul_eq_zero] at H
  obtain H1 | H2 := H
  · -- case 1: x1 - x2 = 0
    addarith [H1]
  · -- case 2: x1 ^2 + x1 * x2 + x2 ^ 2  = 0
    by_cases hx1 : x1 = 0
    · -- case 2a: x1 = 0
      have hx2 :=
      calc x2 ^ 3 = x1 ^ 3 := by rw [hx]
        _ = 0 ^ 3 := by rw [hx1]
        _ = 0 := by numbers
      cancel 3 at hx2
      calc x1 = 0 := by rw [hx1]
        _ = x2 := by rw [hx2]
    · -- case 2b: x1 ≠ 0
      have :=
      calc 0 < x1 ^ 2 + ((x1 + x2) ^ 2 + x2 ^ 2) := by extra
          _ = 2 * (x1 ^ 2 + x1 * x2 + x2 ^ 2) := by ring
          _ = 2 * 0 := by rw [H2]
          _ = 0 := by ring
      numbers at this -- contradiction!

/-! # Exercises -/


example : Injective (fun (x : ℚ) ↦ x - 12) := by
  dsimp [Injective]
  intro x1 x2 hx
  addarith [hx]

example : ¬ Injective (fun (x : ℚ) ↦ x - 12) := by
  sorry


example : Injective (fun (x : ℝ) ↦ 3) := by
  sorry

example : ¬ Injective (fun (x : ℝ) ↦ 3) := by
  dsimp [Injective]
  push_neg
  use 0, 1
  constructor
  · numbers
  · numbers

example : Injective (fun (x : ℚ) ↦ 3 * x - 1) := by
  dsimp [Injective]
  intro x1 x2 hx
  calc
    x1 = ((3 * x1 - 1) + 1) / 3 := by ring
    _ = ((3 * x2 - 1) + 1) / 3 := by rw [hx]
    _ = x2 := by ring

example : ¬ Injective (fun (x : ℚ) ↦ 3 * x - 1) := by
  sorry


example : Injective (fun (x : ℤ) ↦ 3 * x - 1) := by
  dsimp [Injective]
  intro x1 x2 hx
  have :=
    calc
      3 * x1 = (3 * x1 - 1) + 1 := by ring
           _ = (3 * x2 - 1) + 1 := by rw [hx]
           _ = 3 * x2 := by ring

  cancel 3 at this

example : ¬ Injective (fun (x : ℤ) ↦ 3 * x - 1) := by
  sorry


example : Surjective (fun (x : ℝ) ↦ 2 * x) := by
  dsimp [Surjective]
  intro y
  use y / 2
  ring

example : ¬ Surjective (fun (x : ℝ) ↦ 2 * x) := by
  sorry


example : Surjective (fun (x : ℤ) ↦ 2 * x) := by
  sorry

example : ¬ Surjective (fun (x : ℤ) ↦ 2 * x) := by
  dsimp [Surjective]
  push_neg
  use 1
  intro a
  obtain h | h := le_or_succ_le a 0
  · addarith [h]
  · apply ne_of_gt
    calc
      2 * a ≥ 2 * 1 := by rel [h]
      _ > 1 := by numbers

example : Surjective (fun (n : ℕ) ↦ n ^ 2) := by
  sorry

example : ¬ Surjective (fun (n : ℕ) ↦ n ^ 2) := by
  dsimp [Surjective]
  push_neg
  use 2
  intro n
  obtain h | h := le_or_succ_le n 1
  · apply ne_of_lt
    calc
     n ^ 2 ≤ 1 ^ 2 := by rel [h]
     _ < 2 := by numbers
  · apply ne_of_gt
    calc
      n ^ 2 ≥ 2 ^ 2 := by rel [h]
      _ > 2 := by numbers

inductive White
  | meg
  | jack
  deriving DecidableEq

open White

def h : Musketeer → White
  | athos => jack
  | porthos => meg
  | aramis => jack

example : Injective h := by
  sorry

example : ¬ Injective h := by
  dsimp [Injective]
  push_neg
  use aramis, athos
  constructor
  · exhaust
  · exhaust

example : Surjective h := by
  dsimp [Surjective]
  intro y
  cases y
  · use porthos
    exhaust
  · use athos
    exhaust

example : ¬ Surjective h := by
  sorry


def l : White → Musketeer
  | meg => aramis
  | jack => porthos

example : Injective l := by
  dsimp [Injective]
  intro x1 x2 h
  cases x1 <;> cases x2 <;> exhaust

example : ¬ Injective l := by
  sorry


example : Surjective l := by
  sorry


example : ¬ Surjective l := by
  dsimp [Surjective]
  push_neg
  use athos
  intro x
  cases x <;> exhaust

example (f : X → Y) : Injective f ↔ ∀ x1 x2 : X, x1 ≠ x2 → f x1 ≠ f x2 := by
  -- We need to prove that a function `f` is injective if and only if for all `x1` and `x2` in `X`,
  -- if `x1` is not equal to `x2`, then `f x1` is not equal to `f x2`.

  constructor
  -- We split the proof into two directions: (1) If `f` is injective, then the condition holds,
  -- and (2) If the condition holds, then `f` is injective.

  · -- Direction 1: Assume `f` is injective and prove the condition.
    intro h
    -- `h` is the assumption that `f` is injective, i.e., `∀ x1 x2, f x1 = f x2 → x1 = x2`.
    dsimp [Injective] at h
    -- Simplify the definition of `Injective` in `h`.
    intro x1 x2 hne
    -- Assume `x1` and `x2` are distinct elements of `X`.
    intro heq
    -- Assume `f x1 = f x2`.
    have := h heq
    -- From the injectivity of `f`, we get `x1 = x2`.
    contradiction
    -- This contradicts our assumption that `x1 ≠ x2`, so the condition holds.

  · -- Direction 2: Assume the condition holds and prove that `f` is injective.
    intro h
    -- `h` is the assumption that `∀ x1 x2, x1 ≠ x2 → f x1 ≠ f x2`.
    dsimp [Injective]
    -- Simplify the definition of `Injective`.
    intro x1 x2 heq
    -- Assume `f x1 = f x2`.
    by_cases hne : x1 = x2
    -- Consider two cases: either `x1 = x2` or `x1 ≠ x2`.

    · -- Case 1: `x1 = x2`.
      exact hne
      -- If `x1 = x2`, then we are done.

    · -- Case 2: `x1 ≠ x2`.
      have := h x1 x2 hne
      -- From the condition, we get `f x1 ≠ f x2`.
      contradiction
      -- This contradicts our assumption that `f x1 = f x2`, so `x1` must equal `x2`.
      -- Therefore, `f` is injective.


example : ∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ f x + 1) := by
  dsimp [Injective]
  intro f hf x1 x2 h
  apply hf
  addarith [h]

example : ¬ ∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ f x + 1) := by
  sorry


example : ∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ f x + x) := by
  sorry

example : ¬ ∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ f x + x) := by
  -- We need to show that it is not true that for all functions `f : ℚ → ℚ`,
  -- if `f` is injective, then the function `fun x ↦ f x + x` is also injective.

  push_neg
  -- This tactic transforms the goal into finding a specific function `f : ℚ → ℚ`
  -- such that `f` is injective, but `fun x ↦ f x + x` is not injective.

  use fun x ↦ -x
  -- We choose the function `f(x) = -x` as our counterexample.

  constructor
  -- We now need to prove two things:
  -- 1. `f(x) = -x` is injective.
  -- 2. `fun x ↦ f x + x` is not injective.

  · -- Proof that `f(x) = -x` is injective.
    dsimp [Injective]
    -- Simplify the definition of injectivity: we need to show that if `f(x1) = f(x2)`, then `x1 = x2`.
    intro x1 x2 h
    -- Assume `f(x1) = f(x2)`, i.e., `-x1 = -x2`.
    addarith [h]
    -- By adding `x1 + x2` to both sides, we get `x1 = x2`, proving injectivity.

  · -- Proof that `fun x ↦ f x + x` is not injective.
    dsimp [Injective]
    -- Simplify the definition of injectivity: we need to show that there exist `x1` and `x2` such that
    -- `f(x1) + x1 = f(x2) + x2` but `x1 ≠ x2`.
    push_neg
    -- This tactic transforms the goal into finding specific `x1` and `x2` where the function fails to be injective.

    use 1, 0
    -- We choose `x1 = 1` and `x2 = 0` as our counterexample.

    constructor
    -- We now need to show two things:
    -- 1. `f(1) + 1 = f(0) + 0`
    -- 2. `1 ≠ 0`

    · -- Proof that `f(1) + 1 = f(0) + 0`.
      numbers
      -- Since `f(x) = -x`, we have `f(1) + 1 = -1 + 1 = 0` and `f(0) + 0 = 0 + 0 = 0`.
      -- Therefore, `f(1) + 1 = f(0) + 0`.

    · -- Proof that `1 ≠ 0`.
      numbers
      -- This is trivially true since `1` is not equal to `0`.


-- ### Explanation:
-- - **Goal**: The goal is to show that not all functions `f : ℚ → ℚ` that are injective will result in the function `fun x ↦ f x + x` being injective.
-- - **Counterexample**: We use the function `f(x) = -x` as a counterexample. This function is injective, but when we add `x` to it, the resulting function `fun x ↦ -x + x = 0` is not injective.
-- - **Proof Structure**:
--   - First, we prove that `f(x) = -x` is injective.
--   - Then, we show that `fun x ↦ f x + x` is not injective by finding two distinct inputs (`1` and `0`) that map to the same output.

-- This proof demonstrates that even if a function `f` is injective, the function `fun x ↦ f x + x` may not preserve injectivity.


example : ∀ (f : ℤ → ℤ), Surjective f → Surjective (fun x ↦ 2 * f x) := by
  sorry

example : ¬ ∀ (f : ℤ → ℤ), Surjective f → Surjective (fun x ↦ 2 * f x) := by
  push_neg
  use fun x ↦ x
  constructor
  · -- Show `f` is surjective
    intro y
    use y
    rfl
  · -- Show `fun x ↦ 2 * x` is not surjective
    dsimp [Surjective]
    push_neg
    use 1
    intro a
    obtain h | h := le_or_succ_le a 0
    · addarith [h]
    · apply ne_of_gt
      calc
        2 * a ≥ 2 * 1 := by rel [h]
        _ > 1 := by numbers

example : ∀ c : ℝ, Surjective (fun x ↦ c * x) := by
  sorry

example : ¬ ∀ c : ℝ, Surjective (fun x ↦ c * x) := by
  push_neg
  use 0
  dsimp [Surjective]
  push_neg
  use 1
  intro a
  calc
    0 * a = 0 := by ring
    _ ≠ 1 := by numbers

-- We aim to prove that the function `f` is injective given that it is strictly increasing.
example {f : ℚ → ℚ} (hf : ∀ x y, x < y → f x < f y) : Injective f := by
  -- First, we unfold the definition of `Injective`.
  dsimp [Injective]

  -- Assume two arbitrary rational numbers `x1` and `x2` such that `f x1 = f x2`.
  intro x1 x2 h

  -- Use the trichotomy property of rational numbers to consider three cases:
  -- 1. `x1 < x2`
  -- 2. `x1 = x2`
  -- 3. `x1 > x2`
  obtain h1 | h2 | h3 := lt_trichotomy x1 x2

  -- Case 1: `x1 < x2`
  · -- Since `f` is strictly increasing, `f x1 < f x2`.
    have h4 := hf x1 x2 h1

    -- But we know that `f x1 = f x2`, so substituting this into the inequality gives `f x1 < f x1`.
    rw [h] at h4

    -- This is a contradiction because a number cannot be less than itself.
    have := ne_of_lt h4
    contradiction

  -- Case 2: `x1 = x2`
  · -- This is the desired conclusion, so we are done.
    exact h2

  -- Case 3: `x1 > x2`
  · -- Since `f` is strictly increasing, `f x2 < f x1`.
    have h4 := hf x2 x1 h3

    -- But we know that `f x1 = f x2`, so substituting this into the inequality gives `f x2 < f x2`.
    rw [h] at h4

    -- This is a contradiction because a number cannot be less than itself.
    have := ne_of_lt h4
    contradiction

example {f : X → ℕ} {x0 : X} (h0 : f x0 = 0) {i : X → X}
    (hi : ∀ x, f (i x) = f x + 1) : Surjective f := by
  dsimp [Surjective]
  intro b
  simple_induction b with k IH
  · -- base case
    use x0
    exact h0
  · -- inductive step
    obtain ⟨t, ht⟩ := IH
    use i t
    rw [hi, ht]
