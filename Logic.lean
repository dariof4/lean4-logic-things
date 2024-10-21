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
theorem de_morgan : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  apply Iff.intro
  intro 
  

theorem impl_elim : p → q ↔ ¬p ∨ q := by
  apply Iff.intro <;>
  intro h
  by_contra h1
