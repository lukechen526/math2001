/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Exhaust
import Library.Tactic.ModEq

math2001_init


example : Reflexive ((·:ℕ) ∣ ·) := by
  dsimp [Reflexive]
  intro x
  use 1
  ring


example : ¬ Symmetric ((·:ℕ) ∣ ·) := by
  dsimp [Symmetric]
  push_neg
  use 1, 2
  constructor
  · use 2
    numbers
  · apply Nat.not_dvd_of_exists_lt_and_lt
    use 0
    constructor
    · numbers
    · numbers


example : AntiSymmetric ((·:ℕ) ∣ ·) := by
  have H : ∀ {m n}, m = 0 → m ∣ n → m = n
  · intro m n h1 h2
    obtain ⟨k, hk⟩ := h2
    calc m = 0 := by rw [h1]
      _ = 0 * k := by ring
      _ = m * k := by rw [h1]
      _ = n := by rw [hk]
  dsimp [AntiSymmetric]
  intro x y h1 h2
  obtain hx | hx := Nat.eq_zero_or_pos x
  · apply H hx h1
  obtain hy | hy := Nat.eq_zero_or_pos y
  · have : y = x := by apply H hy h2
    rw [this]
  apply le_antisymm
  · apply Nat.le_of_dvd hy h1
  · apply Nat.le_of_dvd hx h2


example : Transitive ((·:ℕ) ∣ ·) := by
  dsimp [Transitive]
  intro a b c hab hbc
  obtain ⟨k, hk⟩ := hab
  obtain ⟨l, hl⟩ := hbc
  use k * l
  calc c = b * l := by rw [hl]
    _ = (a * k) * l := by rw [hk]
    _ = a * (k * l) := by ring


example : Reflexive ((·:ℝ) = ·) := by
  dsimp [Reflexive]
  intro x
  ring

example : Symmetric ((·:ℝ) = ·) := by
  dsimp [Symmetric]
  intro x y h
  rw [h]

example : AntiSymmetric ((·:ℝ) = ·) := by
  dsimp [AntiSymmetric]
  intro x y h1 h2
  rw [h1]

example : Transitive ((·:ℝ) = ·) := by
  dsimp [Transitive]
  intro x y z h1 h2
  rw [h1, h2]


section
local infix:50 "∼" => fun (x y : ℝ) ↦ (x - y) ^ 2 ≤ 1

example : Reflexive (· ∼ ·) := by
  dsimp [Reflexive]
  intro x
  calc (x - x) ^ 2 = 0 := by ring
    _ ≤ 1 := by numbers

example : Symmetric (· ∼ ·) := by
  dsimp [Symmetric]
  intro x y h
  calc (y - x) ^ 2 = (x - y) ^ 2 := by ring
    _ ≤ 1 := by rel [h]

example : ¬ AntiSymmetric (· ∼ ·) := by
  dsimp [AntiSymmetric]
  push_neg
  use 1, 1.1
  constructor
  · numbers
  constructor
  · numbers
  · numbers

example : ¬ Transitive (· ∼ ·) := by
  dsimp [Transitive]
  push_neg
  use 1, 1.9, 2.5
  constructor
  · numbers
  constructor
  · numbers
  · numbers

end


section

inductive Hand
  | rock
  | paper
  | scissors

open Hand


@[reducible] def r : Hand → Hand → Prop
  | rock, rock => False
  | rock, paper => True
  | rock, scissors => False
  | paper, rock => False
  | paper, paper => False
  | paper, scissors => True
  | scissors, rock => True
  | scissors, paper => False
  | scissors, scissors => False

local infix:50 " ≺ " => r


example : ¬ Reflexive (· ≺ ·) := by
  dsimp [Reflexive]
  push_neg
  use rock
  exhaust

example : ¬ Symmetric (· ≺ ·) := by
  dsimp [Symmetric]
  push_neg
  use rock, paper
  exhaust

example : AntiSymmetric (· ≺ ·) := by
  dsimp [AntiSymmetric]
  intro x y
  cases x <;> cases y <;> exhaust

example : ¬ Transitive (· ≺ ·) := by
  dsimp [Transitive]
  push_neg
  use rock, paper, scissors
  exhaust

end

/-! # Exercises -/


example : ¬ Symmetric ((·:ℝ) < ·) := by
  dsimp [Symmetric]
  push_neg
  use 0, 1
  constructor
  · numbers
  · numbers


section
local infix:50 "∼" => fun (x y : ℤ) ↦ x ≡ y [ZMOD 2]

example : ¬ AntiSymmetric (· ∼ ·) := by
  dsimp [AntiSymmetric]
  push_neg
  use 2, 4
  constructor
  · calc
      2 = 0 + 2 * 1 := by ring
      _ ≡ 0 [ZMOD 2] := by extra
      _ ≡ 0 + 2 * 2 [ZMOD 2]:= by extra
      _ ≡ 4 [ZMOD 2] := by numbers
  constructor
  · calc
      4 = 0 + 2 * 2 := by ring
      _ ≡ 0 [ZMOD 2] := by extra
      _ ≡ 0 + 2 * 1 [ZMOD 2]:= by extra
      _ ≡ 2 [ZMOD 2] := by numbers
  · numbers

end

section
inductive Little
  | meg
  | jo
  | beth
  | amy
  deriving DecidableEq

open Little

@[reducible] def s : Little → Little → Prop
  | meg, meg => True
  | meg, jo => True
  | meg, beth => True
  | meg, amy => True
  | jo, meg => True
  | jo, jo => True
  | jo, beth => True
  | jo, amy => False
  | beth, meg => True
  | beth, jo => True
  | beth, beth => False
  | beth, amy => True
  | amy, meg => True
  | amy, jo => False
  | amy, beth => True
  | amy, amy => True

local infix:50 " ∼ " => s


example : Reflexive (· ∼ ·) := by
  sorry

example : ¬ Reflexive (· ∼ ·) := by
  dsimp [Reflexive]
  push_neg
  use beth
  exhaust


example : Symmetric (· ∼ ·) := by
  dsimp [Symmetric]
  intro x y h
  cases x <;> cases y <;> exhaust

example : ¬ Symmetric (· ∼ ·) := by
  sorry

example : AntiSymmetric (· ∼ ·) := by
  sorry

example : ¬ AntiSymmetric (· ∼ ·) := by
  dsimp [AntiSymmetric]
  push_neg
  use meg, jo
  exhaust

example : Transitive (· ∼ ·) := by
  sorry

example : ¬ Transitive (· ∼ ·) := by
  dsimp [Transitive]
  push_neg
  use jo, beth, amy
  exhaust

end


section
local infix:50 "∼" => fun (x y : ℤ) ↦ y ≡ x + 1 [ZMOD 5]

example : Reflexive (· ∼ ·) := by
  sorry

example : ¬ Reflexive (· ∼ ·) := by
  dsimp [Reflexive]
  push_neg
  use 0
  numbers

example : Symmetric (· ∼ ·) := by
  sorry

example : ¬ Symmetric (· ∼ ·) := by
  dsimp [Symmetric]
  push_neg
  use 0, 1
  constructor
  · numbers
  · numbers

example : AntiSymmetric (· ∼ ·) := by
  dsimp [AntiSymmetric]
  intro x y h1 h2
  have h3 : x ≡ x + 1 + 1 [ZMOD 5] := by
    calc
      x ≡ y + 1 [ZMOD 5] := by rel [h2]
      _ ≡ (x + 1) + 1 [ZMOD 5] := by rel [h1]
  have h4 := by
    calc
      0 = x - x := by ring
      _ ≡ (x + 1 + 1) - x [ZMOD 5] := by rel [h3]
      _ = 2 := by ring
  numbers at h4


example : ¬ AntiSymmetric (· ∼ ·) := by
  sorry

example : Transitive (· ∼ ·) := by
  sorry

example : ¬ Transitive (· ∼ ·) := by
  dsimp [Transitive]
  push_neg
  use 0, 1, 2
  constructor
  · numbers
  constructor
  · numbers
  numbers
end


section
local infix:50 "∼" => fun (x y : ℤ) ↦ x + y ≡ 0 [ZMOD 3]

example : Reflexive (· ∼ ·) := by
  sorry

example : ¬ Reflexive (· ∼ ·) := by
  dsimp [Reflexive]
  push_neg
  use 1
  numbers

example : Symmetric (· ∼ ·) := by
  dsimp [Symmetric]
  intro x y h
  calc
    y + x = x + y := by ring
    _ ≡ 0 [ZMOD 3] := h

example : ¬ Symmetric (· ∼ ·) := by
  sorry

example : AntiSymmetric (· ∼ ·) := by
  sorry

example : ¬ AntiSymmetric (· ∼ ·) := by
  dsimp [AntiSymmetric]
  push_neg
  use 1, 2
  constructor
  · use 1
    numbers
  · constructor
    · use 1
      numbers
    · numbers



example : Transitive (· ∼ ·) := by
  sorry

example : ¬ Transitive (· ∼ ·) := by
  dsimp [Transitive]
  push_neg
  use 1, 2, 1
  constructor
  · use 1
    numbers
  · constructor
    · use 1
      numbers
    · numbers

end


example : Reflexive ((· : Set ℕ) ⊆ ·) := by
  dsimp [Reflexive]
  intro x
  dsimp [Set.subset_def]
  intro y h
  exact h

example : ¬ Reflexive ((· : Set ℕ) ⊆ ·) := by
  sorry

example : Symmetric ((· : Set ℕ) ⊆ ·) := by
  sorry

example : ¬ Symmetric ((· : Set ℕ) ⊆ ·) := by
  dsimp [Symmetric]
  push_neg
  use {1}, {1, 2}
  constructor
  · dsimp [Set.subset_def]
    exhaust
  · dsimp [Set.subset_def]
    push_neg
    use 2
    exhaust

example : AntiSymmetric ((· : Set ℕ) ⊆ ·) := by
  dsimp [AntiSymmetric]
  intro x y h1 h2
  dsimp [Set.subset_def] at h1 h2
  ext z
  constructor
  · intro h
    exact h1 z h
  · intro h
    exact h2 z h

example : ¬ AntiSymmetric ((· : Set ℕ) ⊆ ·) := by
  sorry

example : Transitive ((· : Set ℕ) ⊆ ·) := by
  dsimp [Transitive]
  intro x y z h1 h2
  dsimp [Set.subset_def] at *
  intro a h
  exact h2 a (h1 a h)

example : ¬ Transitive ((· : Set ℕ) ⊆ ·) := by
  sorry



section
local infix:50 "≺" => fun ((x1, y1) : ℝ × ℝ) (x2, y2) ↦ (x1 ≤ x2 ∧ y1 ≤ y2)

example : Reflexive (· ≺ ·) := by
  dsimp [Reflexive]
  intro x
  constructor
  · exact le_refl x.1
  · exact le_refl x.2

example : ¬ Reflexive (· ≺ ·) := by
  sorry

example : Symmetric (· ≺ ·) := by
  sorry

example : ¬ Symmetric (· ≺ ·) := by
  dsimp [Symmetric]
  push_neg
  use (1, 1), (2, 2)
  constructor
  · constructor
    · numbers
    · numbers
  · left
    numbers

example : AntiSymmetric (· ≺ ·) := by
  dsimp [AntiSymmetric]
  intro x y hxy hyx
  obtain ⟨hxy', hxy''⟩ := hxy
  obtain ⟨hyx', hyx''⟩ := hyx
  constructor
  · apply le_antisymm
    · exact hxy'
    · exact hyx'
  · apply le_antisymm
    · exact hxy''
    · exact hyx''


example : ¬ AntiSymmetric (· ≺ ·) := by
  sorry

example : Transitive (· ≺ ·) := by
  dsimp [Transitive]
  intro x y z hxy hyz
  obtain ⟨hxy', hxy''⟩ := hxy
  obtain ⟨hyz', hyz''⟩ := hyz
  constructor
  · apply le_trans
    · exact hxy'
    · exact hyz'
  · apply le_trans
    · exact hxy''
    · exact hyz''

example : ¬ Transitive (· ≺ ·) := by
  sorry

end
