/- Copyright (c) Heather Macbeth, 2023-4.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Theory.InjectiveSurjective
import Library.Basic
import AutograderLib

math2001_init
set_option pp.funBinderTypes true

open Function


/-! # Homework 9

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-9,
for clearer statements and any special instructions. -/


/- Problem 1: prove one of these, delete the other -/

@[autogradedProof 4]
theorem problem1a : Surjective (fun (x : ℝ) ↦ 2 * x) := by
  intro y
  use y / 2
  ring



/- Problem 2: prove one of these, delete the other -/


@[autogradedProof 4]
theorem problem2b : ¬ Surjective (fun (x : ℤ) ↦ 2 * x) := by
  intro h_surj
  dsimp [Surjective] at h_surj
  obtain ⟨x, hx⟩ := h_surj 1
  have h_even : Int.Even (2 * x) := by
    use x
    ring
  rw [hx] at h_even
  have h_odd : Int.Odd 1 := by
    use 0
    ring
  rw [Int.odd_iff_not_even] at h_odd
  exact h_odd h_even


/- Problem 3: prove one of these, delete the other -/

@[autogradedProof 4]
theorem problem3a : ∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ f x + 1) := by
  intro f h_inj_f
  intro a₁ a₂ h_eq
  dsimp at h_eq
  have h_f_eq : f a₁ = f a₂ := by
    addarith [h_eq]
  apply h_inj_f h_f_eq



/- Problem 4: prove one of these, delete the other -/

@[autogradedProof 4]
theorem problem4a : Bijective (fun (x : ℝ) ↦ 3 - 2 * x) := by
  constructor
  · -- Injective
    intro x₁ x₂ h_eq
    dsimp at h_eq
    have h : -2 * x₁ = -2 * x₂ := by addarith [h_eq]
    cancel -2 at h
  · -- Surjective
    intro y
    use (3 - y) / 2
    ring



/- Problem 5: prove one of these, delete the other -/


@[autogradedProof 5]
theorem problem5b :
    ¬Injective (fun ((x, y, z) : ℝ × ℝ × ℝ) ↦ (x + y + z, x + 2 * y + 3 * z)) := by
  dsimp [Injective]
  push_neg
  use (1, -2, 1)
  use (0, 0, 0)
  constructor
  · calc
      (fun ((x, y, z) : ℝ × ℝ × ℝ) ↦ (x + y + z, x + 2 * y + 3 * z)) (1, -2, 1)
        = (1 + -2 + 1, 1 + 2 * -2 + 3 * 1) := by rfl
      _ = (0, 0) := by numbers
      _ = (0 + 0 + 0, 0 + 2 * 0 + 3 * 0) := by numbers
      _ = (fun ((x, y, z) : ℝ × ℝ × ℝ) ↦ (x + y + z, x + 2 * y + 3 * z)) (0, 0, 0) := by rfl
  · by_contra h
    injection h with h1 h2
    injection h2 with h3 h4
    numbers at h1


/- Problem 6: prove one of these, delete the other -/

@[autogradedProof 4]
theorem problem6a : Bijective (fun ((r, s) : ℚ × ℚ) ↦ (s, r + 2 * s)) := by
  constructor
  · -- Injective
    intro a₁ a₂ h_eq
    obtain ⟨r₁, s₁⟩ := a₁
    obtain ⟨r₂, s₂⟩ := a₂
    dsimp at h_eq
    injection h_eq with h_s h_r
    rw [h_s] at h_r
    have h_r_simplified : r₁ = r₂ := by addarith [h_r]
    apply Prod.ext
    · exact h_r_simplified
    · exact h_s
  · -- Surjective
    intro b
    obtain ⟨a, b_comp⟩ := b
    use (b_comp - 2 * a, a)
    dsimp
    apply Prod.ext
    · ring
    · ring
