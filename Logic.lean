-- This module serves as the root of the `Logic` library.
-- Import modules here that should be built as part of the library.
import «Logic».Basic
import Mathlib

variable (p q r : Prop)

theorem my_and_comm : p ∧ q ↔ q ∧ p := by
  apply Iff.intro <;>
  intro h <;>
  exact And.intro h.right h.left

theorem my_or_comm : p ∨ q ↔ q ∨ p := by
  apply Iff.intro <;>
  intro h <;>
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq

theorem my_and_assoc : p ∧ (q ∧ r) ↔ (p ∧ q) ∧ r := by
  apply Iff.intro <;>
  intro h
  exact And.intro (And.intro h.left h.right.left) h.right.right
  exact And.intro h.left.left (And.intro h.left.right h.right)

theorem my_or_assoc : p ∨ (q ∨ r) ↔ (p ∨ q) ∨ r := by
  apply Iff.intro <;>
  intro h
  cases h with
  | inl hp => exact Or.inl (Or.inl hp)
  | inr hqr => cases hqr with
    | inl hq => exact Or.inl (Or.inr hq)
    | inr hr => exact Or.inr hr
  cases h with
  | inl hpq => cases hpq with
    | inl hp => exact Or.inl hp
    | inr hq => exact Or.inr (Or.inl hq)
  | inr hr => exact (Or.inr (Or.inr hr))

theorem and_distrib_or : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro <;>
  intro h
  have h2 : q ∨ r := h.right
  cases h2 with
    | inl hq => exact Or.inl (And.intro h.left hq)
    | inr hr => exact Or.inr (And.intro h.left hr)
  cases h with
    | inl hpq => exact And.intro hpq.left (Or.inl hpq.right)
    | inr hpr => exact And.intro hpr.left (Or.inr hpr.right)

theorem or_distrib_and : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  apply Iff.intro <;>
  intro h
  cases h with
    | inl hp => exact And.intro (Or.inl hp) (Or.inl hp)
    | inr hqr => exact And.intro (Or.inr hqr.left) (Or.inr hqr.right)
  have h2 : p ∨ q := h.left
  have h3 : p ∨ r := h.right
  cases h2 with
    | inl hp => exact Or.inl hp
    | inr hq => cases h3 with
      | inl hp => exact Or.inl hp
      | inr hr => exact Or.inr (And.intro hq hr)

theorem d_neg : ¬¬p ↔ p := by
  apply Iff.intro <;>
  intro h <;>
  by_contra h2
  exact h h2
  exact h2 h

theorem compl_or : p ∨ (¬p ∧ q) ↔ p ∨ q := by
  apply Iff.intro <;>
  intro h
  cases h with
  | inl hp => exact Or.inl hp
  | inr hnpq => exact Or.inr hnpq.right
  cases h with
  | inl hp => exact Or.inl hp
  | inr hq => 
    rw [or_distrib_and]
    exact ⟨em p, Or.inr hq⟩

theorem compl_and : p ∧ (¬p ∨ q) ↔ p ∧ q := by
  apply Iff.intro <;>
  intro h
  have h2 := h.right
  cases h2 with
    | inl hnp => by_contra ; exact hnp h.left
    | inr hq => exact ⟨h.left, hq⟩
  exact ⟨h.left, Or.inr h.right⟩
 xs


theorem and_identity : p ∧ True ↔ p := by
  apply Iff.intro <;>
  intro h
  exact h.left
  exact And.intro h True.intro

theorem or_identity : p ∨ False ↔ p := by
  apply Iff.intro <;>
  intro h
  cases h with
    | inl hp => exact hp
    | inr hf => exfalso ; exact hf
  exact Or.inl h

theorem and_absorbtion : p ∨ True ↔ True := by
  apply Iff.intro <;>
  intro h
  exact True.intro
  exact Or.inr h

theorem or_absorbtion : p ∧ False ↔ False := by
  apply Iff.intro <;>
  intro h
  exact h.right
  exfalso
  exact h

theorem my_not_true : ¬True ↔ False := by
  apply Iff.intro <;>
  intro h
  exact h True.intro
  exfalso
  exact h

theorem my_not_false : ¬False ↔ True := by
  apply Iff.intro <;>
  intro h
  exact True.intro
  rw [← my_not_true, d_neg]
  exact h

theorem annulation : p ∧ ¬p ↔ False := by
  apply Iff.intro <;>
  intro h
  exact h.right h.left
  exfalso
  exact h

theorem de_morgan : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by sorry 

theorem impl_elim : p → q ↔ ¬p ∨ q := by
  apply Iff.intro <;>
  intro h
  by_contra h1
  rw [de_morgan, d_neg] at h1
  have h2 := h h1.left
  exact h1.right h2
  intro hp
  cases h with
    | inl h1 => exfalso ; exact h1 hp
    | inr h1 => exact h1
