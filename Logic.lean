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

theorem my_and_assoc : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  apply Iff.intro <;>
  intro h
  exact And.intro h.left.left (And.intro h.left.right h.right)
  exact And.intro (And.intro h.left h.right.left) h.right.right

theorem my_or_assoc : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  apply Iff.intro <;>
  intro h
  cases h with
  | inl hpq => cases hpq with
    | inl hp => exact Or.inl hp
    | inr hq => exact Or.inr (Or.inl hq)
  | inr hr => exact (Or.inr (Or.inr hr))
  cases h with
  | inl hp => exact Or.inl (Or.inl hp)
  | inr hqr => cases hqr with
    | inl hq => exact Or.inl (Or.inr hq)
    | inr hr => exact Or.inr hr

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



theorem and_identity : a ∧ True ↔ a := by
  apply Iff.intro <;>
  intro h
  exact h.left
  exact And.intro h True.intro

theorem or_identity : a ∨ False ↔ a := by
  apply Iff.intro <;>
  intro h
  cases h with
    | inl ha => exact ha
    | inr hf => exfalso ; exact hf
  exact Or.inl h

theorem or_absorbtion : p ∨ True ↔ True := by
  apply Iff.intro <;>
  intro h
  exact True.intro
  exact Or.inr h

theorem and_absorbtion : p ∧ False ↔ False := by
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

theorem excluded_middle : p ∨ ¬p ↔ True := by
  apply Iff.intro <;>
  intro
  exact True.intro
  exact em p

theorem and_de_morgan : ¬(p ∧ q) ↔ ¬p ∨ ¬q := by
  rw [←@or_identity ¬(p∧q), ←@and_absorbtion q, ←@annulation p, ← my_and_assoc, ←@or_identity ((q∧p) ∧ ¬p), ←@and_absorbtion p, ←@annulation q, @my_and_comm q, ←my_and_assoc, ←and_distrib_or]
  nth_rewrite 2 [←@d_neg (p∧q)]
  rw [compl_or, ←@and_identity (¬(p∧q) ∨ ¬p∨¬q), ←@or_absorbtion ¬p, ←@excluded_middle q, ←@my_or_assoc ¬p, ←@compl_or (¬p) q, d_neg, @my_or_comm (¬p) (p∧q), my_or_assoc, my_or_comm, @my_or_comm (p∧q), ←or_distrib_and, my_and_comm, annulation, or_identity]

theorem or_de_morgan : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  symm
  rw [←@and_identity (¬p∧¬q), ←@excluded_middle (p∨q), and_distrib_or, my_and_assoc, @my_or_comm p]
  nth_rewrite 2 [←@d_neg q]
  rw [compl_and, @my_and_comm ¬q, ←my_and_assoc, @my_and_comm ¬p, annulation, my_and_comm, and_absorbtion, my_or_comm, or_identity, my_and_comm, ←compl_and, d_neg, my_or_assoc, or_distrib_and, excluded_middle, @and_distrib_or True, @my_and_comm True, @my_and_comm True, and_identity, and_identity, @my_or_comm p, ←my_or_assoc, excluded_middle, @my_or_comm True, or_absorbtion, and_identity]
