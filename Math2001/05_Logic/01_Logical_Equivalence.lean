/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Basic

math2001_init
set_option pp.funBinderTypes true


example {P Q : Prop} (h1 : P ∨ Q) (h2 : ¬ Q) : P := by
  obtain hP | hQ := h1
  · apply hP
  · contradiction


example (P Q : Prop) : P → (P ∨ ¬ Q) := by
  intro hP
  left
  apply hP


#truth_table ¬(P ∧ ¬ Q)

#truth_table P ↔ (¬ P ∨ Q)


example (P : Prop) : (P ∨ P) ↔ P := by
  constructor
  · intro h
    obtain h1 | h2 := h
    · apply h1
    · apply h2
  · intro h
    left
    apply h


example (P Q R : Prop) : (P ∧ (Q ∨ R)) ↔ ((P ∧ Q) ∨ (P ∧ R)) := by
  constructor
  · intro h
    obtain ⟨h1, h2 | h2⟩ := h
    · left
      constructor
      · apply h1
      · apply h2
    · right
      constructor
      · apply h1
      · apply h2
  · intro h
    obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := h
    · constructor
      · apply h1
      · left
        apply h2
    · constructor
      · apply h1
      · right
        apply h2

#truth_table P ∧ (Q ∨ R)
#truth_table (P ∧ Q) ∨ (P ∧ R)


example {P Q : α → Prop} (h1 : ∀ x : α, P x) (h2 : ∀ x : α, Q x) :
    ∀ x : α, P x ∧ Q x := by
  intro x
  constructor
  · apply h1
  · apply h2


example {P : α → β → Prop} (h : ∃ x : α, ∀ y : β, P x y) :
    ∀ y : β, ∃ x : α, P x y := by
  obtain ⟨x, hx⟩ := h
  intro y
  use x
  apply hx


example (P : α → Prop) : ¬ (∃ x, P x) ↔ ∀ x, ¬ P x := by
  constructor
  · intro h a ha
    have : ∃ x, P x
    · use a
      apply ha
    contradiction
  · intro h h'
    obtain ⟨x, hx⟩ := h'
    have : ¬ P x := h x
    contradiction

/-! # Exercises -/


example {P Q : Prop} (h : P ∧ Q) : P ∨ Q := by
  obtain ⟨hP, hQ⟩ := h
  left
  apply hP


example {P Q R : Prop} (h1 : P → Q) (h2 : P → R) (h3 : P) : Q ∧ R := by
  constructor
  · apply h1
    apply h3
  · apply h2
    apply h3

example (P : Prop) : ¬(P ∧ ¬ P) := by
  intro h
  obtain ⟨hP, hnP⟩ := h
  apply hnP
  apply hP

example {P Q : Prop} (h1 : P ↔ ¬ Q) (h2 : Q) : ¬ P := by
  intro h
  rw [h1] at h
  contradiction

example {P Q : Prop} (h1 : P ∨ Q) (h2 : Q → P) : P := by
  obtain hP | hQ := h1
  · apply hP
  · apply h2
    apply hQ

example {P Q R : Prop} (h : P ↔ Q) : (P ∧ R) ↔ (Q ∧ R) := by
  constructor
  · intro h'
    obtain ⟨hP, hR⟩ := h'
    constructor
    · rw [← h]
      apply hP
    · apply hR
  · intro h'
    obtain ⟨hQ, hR⟩ := h'
    constructor
    · rw [h]
      apply hQ
    · apply hR

example (P : Prop) : (P ∧ P) ↔ P := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := h
    apply h1
  · intro h
    constructor
    · apply h
    · apply h


example (P Q : Prop) : (P ∨ Q) ↔ (Q ∨ P) := by
  constructor
  · intro h
    obtain hP | hQ := h
    · right
      apply hP
    · left
      apply hQ
  · intro h
    obtain hQ | hP := h
    · right
      apply hQ
    · left
      apply hP

example (P Q : Prop) : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := by
  constructor
  · intro h
    constructor
    · intro hP
      have : P ∨ Q
      · left
        apply hP
      contradiction
    · intro hQ
      have : P ∨ Q
      · right
        apply hQ
      contradiction

example {P Q : α → Prop} (h1 : ∀ x, P x → Q x) (h2 : ∀ x, P x) : ∀ x, Q x := by
  intro x
  apply h1
  apply h2

example {P Q : α → Prop} (h : ∀ x, P x ↔ Q x) : (∃ x, P x) ↔ (∃ x, Q x) := by
  constructor
  · intro h'
    obtain ⟨x, hx⟩ := h'
    use x
    rw [← h]
    apply hx
  · intro h'
    obtain ⟨x, hx⟩ := h'
    use x
    rw [h]
    apply hx

example (P : α → β → Prop) : (∃ x y, P x y) ↔ ∃ y x, P x y := by
  constructor
  · intro h
    obtain ⟨x, y, hxy⟩ := h
    use y
    use x
    apply hxy
  · intro h
    obtain ⟨y, x, hxy⟩ := h
    use x
    use y
    apply hxy

example (P : α → β → Prop) : (∀ x y, P x y) ↔ ∀ y x, P x y := by
  constructor
  · intro h
    intro y
    intro x
    apply h
  · intro h
    intro x
    intro y
    apply h

example (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  constructor
  · intro h
    obtain ⟨hP, hQ⟩ := h
    obtain ⟨x, hx⟩ := hP
    use x
    constructor
    · apply hx
    · apply hQ
  · intro h
    obtain ⟨x, hx⟩ := h
    obtain ⟨hP, hQ⟩ := hx
    constructor
    · use x
      apply hP
    · apply hQ
