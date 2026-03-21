/- Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz -/

import Semigroup.GreensRelations.Defs
import Mathlib.Data.Setoid.Basic
import Mathlib.Algebra.Group.Opposite

/-!
# Basic Properties of Green's Relations

This file proves the foundational equivalences and duality properties of Green's relations,
establishing them as setoids over a semigroup.

## Main results
* Reflexivity, symmetry, and transitivity proofs
    for the divisibility relations and Green's relations.
* `Setoid` instances for `IsGreenL`, `IsGreenR`, `IsGreenH`, `IsGreenD`, and `IsGreenJ`.
* Duality lemmas mapping relations in `S` to their counterparts in the opposite semigroup `Sᵐᵒᵖ`.
* `isGreenL_commutes_isGreenR`: Proof that Green's L and R relations commute.

## References
* [T. Colombet, *The Factorization Forest Theorem*][colombet2008]

## Tags
green's relations, semigroup, setoid, duality, opposite semigroup
-/

variable {S : Type*} [Semigroup S]

section Duality

open MulOpposite

/-- Left and right divisibility are dual under the opposite semigroup. -/
lemma isGreenRightDvd_iff_isGreenLeftDvd_op {a b : S} :
    IsGreenRightDvd a b ↔ IsGreenLeftDvd (op a) (op b) := by
  constructor
  · rintro (rfl | ⟨z, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨op z, rfl⟩
  · rintro (h | ⟨z, h⟩)
    · exact Or.inl (op_injective h)
    · exact Or.inr ⟨unop z, op_injective h⟩

/-- Left and right divisibility are dual under the opposite semigroup. -/
lemma isGreenLeftDvd_iff_isGreenRightDvd_op {a b : S} :
    IsGreenLeftDvd a b ↔ IsGreenRightDvd (op a) (op b) := by
  constructor
  · rintro (rfl | ⟨z, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨op z, rfl⟩
  · rintro (h | ⟨z, h⟩)
    · exact Or.inl (op_injective h)
    · exact Or.inr ⟨unop z, op_injective h⟩

/-- Green's L and R relations are dual under the opposite semigroup. -/
lemma isGreenR_iff_isGreenL_op {a b : S} :
    IsGreenR a b ↔ IsGreenL (op a) (op b) := by
  simp only [IsGreenR, IsGreenL, isGreenRightDvd_iff_isGreenLeftDvd_op]

/-- Green's L and R relations are dual under the opposite semigroup. -/
lemma isGreenL_iff_isGreenR_op {a b : S} :
    IsGreenL a b ↔ IsGreenR (op a) (op b) := by
  simp only [IsGreenL, IsGreenR, isGreenLeftDvd_iff_isGreenRightDvd_op]

end Duality


section Equivalences

namespace IsGreenLeftDvd

/-- Left divisibility is reflexive. -/
@[simp, refl] theorem refl (a : S) : IsGreenLeftDvd a a := Or.inl rfl

/-- Left divisibility is transitive. -/
@[trans] theorem trans {a b c : S} (hab : IsGreenLeftDvd a b)
    (hbc : IsGreenLeftDvd b c) : IsGreenLeftDvd a c := by
  rcases hab with rfl | ⟨x, hx⟩
  · exact hbc
  · rcases hbc with rfl | ⟨y, hy⟩
    · exact Or.inr ⟨x, hx⟩
    · exact Or.inr ⟨x * y, by rw [hx, hy, mul_assoc]⟩

end IsGreenLeftDvd

namespace IsGreenRightDvd

/-- Right divisibility is reflexive. -/
@[simp, refl] theorem refl (a : S) : IsGreenRightDvd a a := Or.inl rfl

open MulOpposite in
/-- Right divisibility is transitive. -/
@[trans] theorem trans {a b c : S} (hab : IsGreenRightDvd a b)
    (hbc : IsGreenRightDvd b c) : IsGreenRightDvd a c := by
  rw [isGreenRightDvd_iff_isGreenLeftDvd_op] at hab hbc ⊢
  exact IsGreenLeftDvd.trans hab hbc

end IsGreenRightDvd

namespace IsGreenJRel

/-- The basic J-relation step is reflexive. -/
@[simp, refl] theorem refl (a : S) : IsGreenJRel a a := eq rfl

/-- The basic J-relation step is transitive. -/
@[trans] theorem trans {a b c : S} (hab : IsGreenJRel a b)
    (hbc : IsGreenJRel b c) : IsGreenJRel a c := by
  cases hab
  case eq h => exact h ▸ hbc
  case mul_left u1 h1 =>
    cases hbc
    case eq h2 => exact h2.symm ▸ mul_left u1 h1
    case mul_left u2 h2 => exact mul_left (u1 * u2) (by simp [h1, h2, mul_assoc])
    case mul_right v2 h2 => exact mul_both u1 v2 (by simp [h1, h2, mul_assoc])
    case mul_both u2 v2 h2 => exact mul_both (u1 * u2) v2 (by simp [h1, h2, mul_assoc])
  case mul_right v1 h1 =>
    cases hbc
    case eq h2 => exact h2.symm ▸ mul_right v1 h1
    case mul_left u2 h2 => exact mul_both u2 v1 (by simp [h1, h2, mul_assoc])
    case mul_right v2 h2 => exact mul_right (v2 * v1) (by simp [h1, h2, mul_assoc])
    case mul_both u2 v2 h2 => exact mul_both u2 (v2 * v1) (by simp [h1, h2, mul_assoc])
  case mul_both u1 v1 h1 =>
    cases hbc
    case eq h2 => exact h2.symm ▸ mul_both u1 v1 h1
    case mul_left u2 h2 => exact mul_both (u1 * u2) v1 (by simp [h1, h2, mul_assoc])
    case mul_right v2 h2 => exact mul_both u1 (v2 * v1) (by simp [h1, h2, mul_assoc])
    case mul_both u2 v2 h2 => exact mul_both (u1 * u2) (v2 * v1) (by simp [h1, h2, mul_assoc])

end IsGreenJRel

namespace IsGreenL

/-- Green's L relation is reflexive. -/
@[simp, refl] theorem refl (a : S) : IsGreenL a a := ⟨IsGreenLeftDvd.refl a, IsGreenLeftDvd.refl a⟩

/-- Green's L relation is symmetric. -/
@[symm] theorem symm {a b : S} (h : IsGreenL a b) : IsGreenL b a := ⟨h.right, h.left⟩

/-- Green's L relation is transitive. -/
@[trans] theorem trans {a b c : S} (hab : IsGreenL a b) (hbc : IsGreenL b c) : IsGreenL a c :=
  ⟨IsGreenLeftDvd.trans hab.left hbc.left, IsGreenLeftDvd.trans hbc.right hab.right⟩

/-- Green's L relation defines a setoid on `S`. -/
protected def setoid (S : Type*) [Semigroup S] : Setoid S where
  r := IsGreenL
  iseqv := { refl := refl, symm := symm, trans := trans }

/-- Green's L relation is preserved by right multiplication. -/
theorem mul_right (c : S) {a b : S} (h : IsGreenL a b) : IsGreenL (a * c) (b * c) := by
  rcases h with ⟨h1, h2⟩
  constructor
  · rcases h1 with rfl | ⟨z, hz⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨z, by rw [hz, mul_assoc]⟩
  · rcases h2 with rfl | ⟨z, hz⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨z, by rw [hz, mul_assoc]⟩

/-- Right cancellation property for elements related by Green's L relation. -/
@[simp] theorem cancellation {a x u v : S} (hx : IsGreenL x a) (h_cancel : a * u * v = a) :
    x * u * v = x := by
  rcases hx.left with rfl | ⟨k, rfl⟩
  · exact h_cancel
  · simp only [mul_assoc, h_cancel]

end IsGreenL

namespace IsGreenR

/-- Green's R relation is reflexive. -/
@[simp, refl] theorem refl (a : S) : IsGreenR a a :=
  ⟨IsGreenRightDvd.refl a, IsGreenRightDvd.refl a⟩

/-- Green's R relation is symmetric. -/
@[symm] theorem symm {a b : S} (h : IsGreenR a b) : IsGreenR b a := ⟨h.right, h.left⟩

/-- Green's R relation is transitive. -/
@[trans] theorem trans {a b c : S} (hab : IsGreenR a b) (hbc : IsGreenR b c) : IsGreenR a c :=
  ⟨IsGreenRightDvd.trans hab.left hbc.left, IsGreenRightDvd.trans hbc.right hab.right⟩

/-- Green's R relation defines a setoid on `S`. -/
protected def setoid (S : Type*) [Semigroup S] : Setoid S where
  r := IsGreenR
  iseqv := { refl := refl, symm := symm, trans := trans }

open MulOpposite in
/-- Green's R relation is preserved by left multiplication. -/
theorem mul_left (c : S) {a b : S} (h : IsGreenR a b) : IsGreenR (c * a) (c * b) := by
  rw [isGreenR_iff_isGreenL_op] at h ⊢
  exact IsGreenL.mul_right (op c) h

/-- Left cancellation property for elements related by Green's R relation. -/
@[simp] theorem cancellation {a x u v : S} (hx : IsGreenR x a) (h_cancel : v * u * a = a) :
    v * u * x = x := by
  rcases hx.left with rfl | ⟨k, rfl⟩
  · exact h_cancel
  · simp only [← mul_assoc, h_cancel]

end IsGreenR

namespace IsGreenH

/-- Green's H relation is reflexive. -/
@[simp, refl] theorem refl (a : S) : IsGreenH a a := ⟨IsGreenL.refl a, IsGreenR.refl a⟩

/-- Green's H relation is symmetric. -/
@[symm] theorem symm {a b : S} (h : IsGreenH a b) : IsGreenH b a :=
    ⟨IsGreenL.symm h.left, IsGreenR.symm h.right⟩

/-- Green's H relation is transitive. -/
@[trans] theorem trans {a b c : S} (hab : IsGreenH a b) (hbc : IsGreenH b c) : IsGreenH a c :=
  ⟨IsGreenL.trans hab.left hbc.left, IsGreenR.trans hab.right hbc.right⟩

/-- Green's H relation defines a setoid on `S`. -/
protected def setoid (S : Type*) [Semigroup S] : Setoid S where
  r := IsGreenH
  iseqv := { refl := refl, symm := symm, trans := trans }

open MulOpposite in
/-- Green's H relation is self-dual under the opposite semigroup. -/
lemma isGreenH_iff_isGreenH_op {a b : S} :
    IsGreenH a b ↔ IsGreenH (op a) (op b) := by
  constructor
  · rintro ⟨hL, hR⟩
    exact ⟨isGreenR_iff_isGreenL_op.mp hR, isGreenL_iff_isGreenR_op.mp hL⟩
  · rintro ⟨hL_op, hR_op⟩
    exact ⟨isGreenL_iff_isGreenR_op.mpr hR_op, isGreenR_iff_isGreenL_op.mpr hL_op⟩

end IsGreenH

/-- Green's L and R relations commute: `L ∘ R = R ∘ L`. -/
lemma isGreenL_commutes_isGreenR {a b z : S} (hL : IsGreenL a z) (hR : IsGreenR z b) :
    ∃ z', IsGreenR a z' ∧ IsGreenL z' b := by
  have h_az : IsGreenLeftDvd a z := hL.left
  have h_za : IsGreenLeftDvd z a := hL.right
  have h_zb : IsGreenRightDvd z b := hR.left
  have h_bz : IsGreenRightDvd b z := hR.right
  rcases h_az with rfl | ⟨u, hu⟩
  · exact ⟨b, hR, IsGreenL.refl b⟩
  rcases h_za with rfl | ⟨v, hv⟩
  · exact ⟨b, hR, IsGreenL.refl b⟩
  rcases h_zb with rfl | ⟨x, hx⟩
  · exact ⟨a, IsGreenR.refl a, hL⟩
  rcases h_bz with rfl | ⟨y, hy⟩
  · exact ⟨a, IsGreenR.refl a, hL⟩
  use a * y
  have hR1 : IsGreenRightDvd a (a * y) := by
    right; use x; rw [hu, mul_assoc u z y, ← hy, mul_assoc u b x, ← hx]
  have hR2 : IsGreenRightDvd (a * y) a := by
    right; exact ⟨y, rfl⟩
  have hL1 : IsGreenLeftDvd (a * y) b := by
    right; use u; rw [hu, mul_assoc, ← hy]
  have hL2 : IsGreenLeftDvd b (a * y) := by
    right; use v; rw [← mul_assoc, ← hv, hy]
  exact ⟨⟨hR1, hR2⟩, ⟨hL1, hL2⟩⟩

namespace IsGreenD

/-- Green's D relation is reflexive. -/
@[simp, refl] theorem refl (a : S) : IsGreenD a a := ⟨a, IsGreenL.refl a, IsGreenR.refl a⟩

/-- Green's D relation is symmetric. -/
@[symm] theorem symm {a b : S} (h : IsGreenD a b) : IsGreenD b a := by
  obtain ⟨z, hL, hR⟩ := h
  obtain ⟨z', h_x_R_z', h_z'_L_y⟩ := isGreenL_commutes_isGreenR hL hR
  exact ⟨z', IsGreenL.symm h_z'_L_y, IsGreenR.symm h_x_R_z'⟩

/-- Green's D relation is transitive. -/
@[trans] theorem trans {a b c : S} (hab : IsGreenD a b)
    (hbc : IsGreenD b c) : IsGreenD a c := by
  obtain ⟨z1, h_x_L_z1, h_z1_R_y⟩ := hab
  obtain ⟨z2, h_y_L_z2, h_z2_R_z⟩ := hbc
  have h_z2_L_y : IsGreenL z2 b := IsGreenL.symm h_y_L_z2
  have h_y_R_z1 : IsGreenR b z1 := IsGreenR.symm h_z1_R_y
  obtain ⟨z3, h_z2_R_z3, h_z3_L_z1⟩ := isGreenL_commutes_isGreenR h_z2_L_y h_y_R_z1
  have h_z1_L_z3 : IsGreenL z1 z3 := IsGreenL.symm h_z3_L_z1
  have h_z3_R_z2 : IsGreenR z3 z2 := IsGreenR.symm h_z2_R_z3
  have h_x_L_z3 : IsGreenL a z3 := IsGreenL.trans h_x_L_z1 h_z1_L_z3
  have h_z3_R_z : IsGreenR z3 c := IsGreenR.trans h_z3_R_z2 h_z2_R_z
  exact ⟨z3, h_x_L_z3, h_z3_R_z⟩

/-- Green's D relation defines a setoid on `S`. -/
protected def setoid (S : Type*) [Semigroup S] : Setoid S where
  r := IsGreenD
  iseqv := { refl := refl, symm := symm, trans := trans }

open MulOpposite in
/-- Green's D relation is self-dual under the opposite semigroup. -/
lemma isGreenD_iff_isGreenD_op {a b : S} :
    IsGreenD a b ↔ IsGreenD (op a) (op b) := by
  constructor
  · rintro ⟨z, hL, hR⟩
    obtain ⟨z', hR', hL'⟩ := isGreenL_commutes_isGreenR hL hR
    exact ⟨op z', isGreenR_iff_isGreenL_op.mp hR', isGreenL_iff_isGreenR_op.mp hL'⟩
  · rintro ⟨z, hL, hR⟩
    have h1 : IsGreenR a (unop z) := isGreenR_iff_isGreenL_op.mpr hL
    have h2 : IsGreenL (unop z) b := isGreenL_iff_isGreenR_op.mpr hR
    obtain ⟨z', hR_bz', hL_z'a⟩ := isGreenL_commutes_isGreenR (IsGreenL.symm h2) (IsGreenR.symm h1)
    exact ⟨z', IsGreenL.symm hL_z'a, IsGreenR.symm hR_bz'⟩

end IsGreenD

namespace IsGreenJ

/-- Green's J relation is reflexive. -/
@[simp, refl] theorem refl (a : S) : IsGreenJ a a := ⟨IsGreenJRel.refl a, IsGreenJRel.refl a⟩

/-- Green's J relation is symmetric. -/
@[symm] theorem symm {a b : S} (h : IsGreenJ a b) : IsGreenJ b a := ⟨h.right, h.left⟩

/-- Green's J relation is transitive. -/
@[trans] theorem trans {a b c : S} (hab : IsGreenJ a b) (hbc : IsGreenJ b c) : IsGreenJ a c :=
  ⟨IsGreenJRel.trans hab.left hbc.left, IsGreenJRel.trans hbc.right hab.right⟩

/-- Green's J relation defines a setoid on `S`. -/
protected def setoid (S : Type*) [Semigroup S] : Setoid S where
  r := IsGreenJ
  iseqv := { refl := refl, symm := symm, trans := trans }

end IsGreenJ

end Equivalences
