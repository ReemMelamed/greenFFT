/- Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz -/

import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Algebra.Group.Opposite

/-!
# Green's Relations

This file defines Green's relations (L, R, H, D, and J) on a general semigroup `S` and proves
their fundamental properties. It also explores regular D-classes, idempotents,
and the coincidence of the D and J relations in finite semigroups.

## Main definitions
* `IsGreenL`, `IsGreenR`, `IsGreenH`, `IsGreenD`, `IsGreenJ`: Green's relations.
* `GreenLClass`, `GreenRClass`, `GreenHClass`,
  `GreenDClass`, `GreenJClass`: The equivalence classes.
* `IsGreenRegular`: An element `a` is regular if `a * s * a = a` for some `s`.
* `IsRegularDClass`: A D-class where every element is regular.

## Main statements
* `isGreenL_commutes_isGreenR`: Green's L and R relations commute.
* `equivHClassOfIsGreenR`, `equivHClassOfIsGreenL`: Bijections between H-classes.
* `isGreenD_eq_isGreenJ_of_finite`: In a finite semigroup, Green's D and J relations coincide.
* `isGroup_isGreenH_eqvClass_iff_idempotent`:
  An H-class is a group if and only if it contains an idempotent.

## References
* Colombet, T. (2008). The Factorisation Forest Theorem.
-/

variable {S : Type*} [Semigroup S]

section GreenDefinitions

/-- `IsGreenLeftDvd a b` means that `a` is a left multiple of `b`,
  i.e., `a = b` or `a = z * b`. -/
def IsGreenLeftDvd (a b : S) := a = b ∨ ∃ z, a = z * b

/-- `IsGreenRightDvd a b` means that `a` is a right multiple of `b`,
  i.e., `a = b` or `a = b * z`. -/
def IsGreenRightDvd (a b : S) := a = b ∨ ∃ z, a = b * z

/-- `IsGreenJRel a b` represents the basic step of being a two-sided multiple.
`a` is related to `b` if `a = b`, `a = u * b`, `a = b * v`, or `a = u * b * v`. -/
inductive IsGreenJRel (a b : S) : Prop
  | eq (h : a = b)
  | mul_left (u : S) (h : a = u * b)
  | mul_right (v : S) (h : a = b * v)
  | mul_both (u v : S) (h : a = u * b * v)

/-- Green's L relation: `a` and `b` generate the same principal left ideal. -/
def IsGreenL (a b : S) := IsGreenLeftDvd a b ∧ IsGreenLeftDvd b a

/-- Green's R relation: `a` and `b` generate the same principal right ideal. -/
def IsGreenR (a b : S) := IsGreenRightDvd a b ∧ IsGreenRightDvd b a

/-- Green's H relation: the intersection of Green's L and Green's R relations. -/
def IsGreenH (a b : S) := IsGreenL a b ∧ IsGreenR a b

/-- Green's D relation: the join of Green's L and Green's R relations.
Here defined explicitly as the existence of an intermediate element `z`. -/
def IsGreenD (a b : S) := ∃ z, IsGreenL a z ∧ IsGreenR z b

/-- Green's J relation: `a` and `b` generate the same principal two-sided ideal. -/
def IsGreenJ (a b : S) := IsGreenJRel a b ∧ IsGreenJRel b a

open MulOpposite in
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

open MulOpposite in
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

open MulOpposite in
/-- Green's L and R relations are dual under the opposite semigroup. -/
lemma isGreenR_iff_isGreenL_op {a b : S} :
    IsGreenR a b ↔ IsGreenL (op a) (op b) := by
  simp only [IsGreenR, IsGreenL, isGreenRightDvd_iff_isGreenLeftDvd_op]

open MulOpposite in
/-- Green's L and R relations are dual under the opposite semigroup. -/
lemma isGreenL_iff_isGreenR_op {a b : S} :
    IsGreenL a b ↔ IsGreenR (op a) (op b) := by
  simp only [IsGreenL, IsGreenR, isGreenLeftDvd_iff_isGreenRightDvd_op]

end GreenDefinitions



section GreenEquivalences

namespace IsGreenLeftDvd

/-- Left divisibility is reflexive. -/
@[refl] theorem refl (a : S) : IsGreenLeftDvd a a := Or.inl rfl

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
@[refl] theorem refl (a : S) : IsGreenRightDvd a a := Or.inl rfl

open MulOpposite in
/-- Right divisibility is transitive. -/
@[trans] theorem trans {a b c : S} (hab : IsGreenRightDvd a b)
    (hbc : IsGreenRightDvd b c) : IsGreenRightDvd a c := by
  rw [isGreenRightDvd_iff_isGreenLeftDvd_op] at hab hbc ⊢
  exact IsGreenLeftDvd.trans hab hbc

end IsGreenRightDvd


namespace IsGreenJRel

/-- The basic J-relation step is reflexive. -/
@[refl] theorem refl (a : S) : IsGreenJRel a a := eq rfl

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
@[refl] theorem refl (a : S) : IsGreenL a a :=
  ⟨IsGreenLeftDvd.refl a, IsGreenLeftDvd.refl a⟩

/-- Green's L relation is symmetric. -/
@[symm] theorem symm {a b : S} (h : IsGreenL a b) : IsGreenL b a :=
  ⟨h.right, h.left⟩

/-- Green's L relation is transitive. -/
@[trans] theorem trans {a b c : S} (hab : IsGreenL a b) (hbc : IsGreenL b c) : IsGreenL a c :=
  ⟨IsGreenLeftDvd.trans hab.left hbc.left, IsGreenLeftDvd.trans hbc.right hab.right⟩

/-- Green's L relation defines a setoid on `S`. -/
protected def setoid (S : Type*) [Semigroup S] : Setoid S where
  r := IsGreenL
  iseqv := {
    refl := refl
    symm := symm
    trans := trans
  }

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
theorem cancellation {a x u v : S} (hx : IsGreenL x a) (h_cancel : a * u * v = a) :
    x * u * v = x := by
  rcases hx.left with rfl | ⟨k, rfl⟩
  · exact h_cancel
  · simp only [mul_assoc, h_cancel]

end IsGreenL


namespace IsGreenR

/-- Green's R relation is reflexive. -/
@[refl] theorem refl (a : S) : IsGreenR a a :=
  ⟨IsGreenRightDvd.refl a, IsGreenRightDvd.refl a⟩

/-- Green's R relation is symmetric. -/
@[symm] theorem symm {a b : S} (h : IsGreenR a b) : IsGreenR b a :=
  ⟨h.right, h.left⟩

/-- Green's R relation is transitive. -/
@[trans] theorem trans {a b c : S} (hab : IsGreenR a b) (hbc : IsGreenR b c) : IsGreenR a c :=
  ⟨IsGreenRightDvd.trans hab.left hbc.left, IsGreenRightDvd.trans hbc.right hab.right⟩

/-- Green's R relation defines a setoid on `S`. -/
protected def setoid (S : Type*) [Semigroup S] : Setoid S where
  r := IsGreenR
  iseqv := {
    refl := refl
    symm := symm
    trans := trans
  }

open MulOpposite in
/-- Green's R relation is preserved by left multiplication. -/
theorem mul_left (c : S) {a b : S} (h : IsGreenR a b) : IsGreenR (c * a) (c * b) := by
  rw [isGreenR_iff_isGreenL_op] at h ⊢
  exact IsGreenL.mul_right (op c) h

/-- Left cancellation property for elements related by Green's R relation. -/
theorem cancellation {a x u v : S} (hx : IsGreenR x a) (h_cancel : v * u * a = a) :
    v * u * x = x := by
  rcases hx.left with rfl | ⟨k, rfl⟩
  · exact h_cancel
  · simp only [← mul_assoc, h_cancel]

end IsGreenR


namespace IsGreenH

/-- Green's H relation is reflexive. -/
@[refl] theorem refl (a : S) : IsGreenH a a :=
  ⟨IsGreenL.refl a, IsGreenR.refl a⟩

/-- Green's H relation is symmetric. -/
@[symm] theorem symm {a b : S} (h : IsGreenH a b) : IsGreenH b a :=
  ⟨IsGreenL.symm h.left, IsGreenR.symm h.right⟩

/-- Green's H relation is transitive. -/
@[trans] theorem trans {a b c : S} (hab : IsGreenH a b) (hbc : IsGreenH b c) : IsGreenH a c :=
  ⟨IsGreenL.trans hab.left hbc.left, IsGreenR.trans hab.right hbc.right⟩

/-- Green's H relation defines a setoid on `S`. -/
protected def setoid (S : Type*) [Semigroup S] : Setoid S where
  r := IsGreenH
  iseqv := {
    refl := refl
    symm := symm
    trans := trans
  }

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
@[refl] theorem refl (a : S) : IsGreenD a a :=
  ⟨a, IsGreenL.refl a, IsGreenR.refl a⟩

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
  iseqv := {
    refl := refl
    symm := symm
    trans := trans
  }

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
@[refl] theorem refl (a : S) : IsGreenJ a a :=
  ⟨IsGreenJRel.refl a, IsGreenJRel.refl a⟩

/-- Green's J relation is symmetric. -/
@[symm] theorem symm {a b : S} (h : IsGreenJ a b) : IsGreenJ b a :=
  ⟨h.right, h.left⟩

/-- Green's J relation is transitive. -/
@[trans] theorem trans {a b c : S} (hab : IsGreenJ a b) (hbc : IsGreenJ b c) : IsGreenJ a c :=
  ⟨IsGreenJRel.trans hab.left hbc.left, IsGreenJRel.trans hbc.right hab.right⟩

/-- Green's J relation defines a setoid on `S`. -/
protected def setoid (S : Type*) [Semigroup S] : Setoid S where
  r := IsGreenJ
  iseqv := {
    refl := refl
    symm := symm
    trans := trans
  }

end IsGreenJ

end GreenEquivalences



section GreenClasses

namespace IsGreenL
/-- The equivalence class of `x` under Green's L relation. -/
def eqvClass (x : S) : Set S := setOf (IsGreenL · x)
end IsGreenL

namespace IsGreenR
/-- The equivalence class of `x` under Green's R relation. -/
def eqvClass (x : S) : Set S := setOf (IsGreenR · x)
end IsGreenR

namespace IsGreenH
/-- The equivalence class of `x` under Green's H relation. -/
def eqvClass (x : S) : Set S := setOf (IsGreenH · x)
end IsGreenH

namespace IsGreenD
/-- The equivalence class of `x` under Green's D relation. -/
def eqvClass (x : S) : Set S := setOf (IsGreenD · x)
end IsGreenD

namespace IsGreenJ
/-- The equivalence class of `x` under Green's J relation. -/
def eqvClass (x : S) : Set S := setOf (IsGreenJ · x)
end IsGreenJ

/-- The quotient type of `S` by Green's L relation. -/
def GreenLClass (S : Type*) [Semigroup S] := Quotient (IsGreenL.setoid S)

namespace GreenLClass
/-- Constructs the Green's L-class of an element `x`. -/
def mk (x : S) : GreenLClass S := Quotient.mk (IsGreenL.setoid S) x
end GreenLClass

/-- The quotient type of `S` by Green's R relation. -/
def GreenRClass (S : Type*) [Semigroup S] := Quotient (IsGreenR.setoid S)

namespace GreenRClass
/-- Constructs the Green's R-class of an element `x`. -/
def mk (x : S) : GreenRClass S := Quotient.mk (IsGreenR.setoid S) x
end GreenRClass

/-- The quotient type of `S` by Green's H relation. -/
def GreenHClass (S : Type*) [Semigroup S] := Quotient (IsGreenH.setoid S)

namespace GreenHClass
/-- Constructs the Green's H-class of an element `x`. -/
def mk (x : S) : GreenHClass S := Quotient.mk (IsGreenH.setoid S) x
end GreenHClass

/-- The quotient type of `S` by Green's D relation. -/
def GreenDClass (S : Type*) [Semigroup S] := Quotient (IsGreenD.setoid S)

namespace GreenDClass
/-- Constructs the Green's D-class of an element `x`. -/
def mk (x : S) : GreenDClass S := Quotient.mk (IsGreenD.setoid S) x
end GreenDClass

/-- The quotient type of `S` by Green's J relation. -/
def GreenJClass (S : Type*) [Semigroup S] := Quotient (IsGreenJ.setoid S)

namespace GreenJClass
/-- Constructs the Green's J-class of an element `x`. -/
def mk (x : S) : GreenJClass S := Quotient.mk (IsGreenJ.setoid S) x
end GreenJClass

/-- An element `a` is regular if there exists `s` such that `a * s * a = a`. -/
def IsGreenRegular (a : S) := ∃ s, a * s * a = a

/-- A D-class is regular if all its elements are regular. -/
def IsRegularDClass (D : Set S) := ∀ x ∈ D, IsGreenRegular x

end GreenClasses



section Helpers

/-- The opposite semigroup construction gives an equivalence between `S` and `Sᵐᵒᵖ`
  that preserves Green's relations, so finiteness of `S` implies finiteness of `Sᵐᵒᵖ`. -/
instance instFiniteMulOpposite [Finite S] : Finite Sᵐᵒᵖ :=
  Finite.of_equiv S MulOpposite.opEquiv

/-- The sequence defined by repeatedly multiplying `a` by `c` on the right. -/
def rightMulSeq (a c : S) : ℕ → S
  | 0 => a
  | n + 1 => rightMulSeq a c n * c

/-- Left multiplication can be pulled out of a `rightMulSeq`. -/
lemma rightMulSeq_mul_pull (c : S) (m : ℕ) (x u : S) :
    rightMulSeq (u * x) c m = u * rightMulSeq x c m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    calc rightMulSeq (u * x) c (m + 1) = rightMulSeq (u * x) c m * c := rfl
      _ = (u * rightMulSeq x c m) * c := by rw [ih]
      _ = u * (rightMulSeq x c m * c) := mul_assoc u (rightMulSeq x c m) c
      _ = u * rightMulSeq x c (m + 1) := rfl

/-- Extracting a right multiplication from the base of a `rightMulSeq`. -/
lemma rightMulSeq_pull_c (c : S) (n : ℕ) (x : S) :
    rightMulSeq x c (n + 1) = rightMulSeq (x * c) c n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc rightMulSeq x c (n + 1 + 1) = rightMulSeq x c (n + 1) * c := rfl
      _ = rightMulSeq (x * c) c n * c := by rw [ih]
      _ = rightMulSeq (x * c) c (n + 1) := rfl

/-- The sequence defined by repeatedly multiplying `a` by `c` on the left. -/
def leftMulSeq (c a : S) : ℕ → S
  | 0 => a
  | n + 1 => c * leftMulSeq c a n

/-- Right multiplication can be pulled out of a `leftMulSeq`. -/
lemma leftMulSeq_mul_pull (c : S) (m : ℕ) (x v : S) :
    leftMulSeq c (x * v) m = leftMulSeq c x m * v := by
  induction m with
  | zero => rfl
  | succ m ih =>
    calc leftMulSeq c (x * v) (m + 1) = c * leftMulSeq c (x * v) m := rfl
      _ = c * (leftMulSeq c x m * v) := by rw [ih]
      _ = (c * leftMulSeq c x m) * v := (mul_assoc c (leftMulSeq c x m) v).symm
      _ = leftMulSeq c x (m + 1) * v := rfl

/-- Extracting a left multiplication from the base of a `leftMulSeq`. -/
lemma leftMulSeq_pull_c (c : S) (n : ℕ) (x : S) :
    leftMulSeq c x (n + 1) = leftMulSeq c (c * x) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc leftMulSeq c x (n + 1 + 1) = c * leftMulSeq c x (n + 1) := rfl
      _ = c * leftMulSeq c (c * x) n := by rw [ih]
      _ = leftMulSeq c (c * x) (n + 1) := rfl

/-- In a finite semigroup, a `leftMulSeq` eventually repeats. -/
lemma leftMulSeq_pigeonhole [Finite S] (c a : S) :
    ∃ i j : ℕ, i < j ∧ leftMulSeq c a i = leftMulSeq c a j := by
  obtain ⟨i, j, h_neq, heq⟩ := Finite.exists_ne_map_eq_of_infinite (leftMulSeq c a)
  rcases lt_trichotomy i j with h_lt | h_eq | h_gt
  · exact ⟨i, j, h_lt, heq⟩
  · exact False.elim (h_neq h_eq)
  · exact ⟨j, i, h_gt, heq.symm⟩

/-- Any element in a `leftMulSeq` starting from `a` is a left multiple of `a`. -/
lemma leftMulSeq_isGreenLeftDvd (c a : S) (m : ℕ) :
    IsGreenLeftDvd (leftMulSeq c a m) a := by
  cases m with
  | zero => exact Or.inl rfl
  | succ m =>
    induction m with
    | zero => exact Or.inr ⟨c, rfl⟩
    | succ m ih =>
      rcases ih with h_eq | ⟨w, hw⟩
      · exact Or.inr ⟨c, by rw [leftMulSeq, h_eq]⟩
      · exact Or.inr ⟨c * w, by rw [leftMulSeq, hw, ← mul_assoc]⟩

/-- Left divisibility is preserved by left multiplication. -/
lemma isGreenLeftDvd_mul_left (a b x : S) (h : IsGreenLeftDvd a b) :
    IsGreenLeftDvd (x * a) b := by
  rcases h with rfl | ⟨w, hw⟩
  · exact Or.inr ⟨x, rfl⟩
  · exact Or.inr ⟨x * w, by rw [hw, ← mul_assoc]⟩

/-- Left and right multiplication sequences commute. -/
lemma leftMulSeq_rightMulSeq_comm (c x d : S) (i k : ℕ) :
    leftMulSeq c (rightMulSeq x d k) i = rightMulSeq (leftMulSeq c x i) d k := by
  induction i with
  | zero => rfl
  | succ i ih =>
    calc leftMulSeq c (rightMulSeq x d k) (i + 1) = c * leftMulSeq c (rightMulSeq x d k) i := rfl
      _ = c * rightMulSeq (leftMulSeq c x i) d k := by rw [ih]
      _ = rightMulSeq (c * leftMulSeq c x i) d k :=
        (rightMulSeq_mul_pull d k (leftMulSeq c x i) c).symm
      _ = rightMulSeq (leftMulSeq c x (i + 1)) d k := rfl

/-- If `b = c * b * d`, applying `n` left steps then `n` right steps yields `b`. -/
lemma b_eq_right_left_seq (c b d : S) (h : b = c * b * d) (n : ℕ) :
    b = rightMulSeq (leftMulSeq c b n) d n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc b = c * b * d := h
      _ = c * rightMulSeq (leftMulSeq c b n) d n * d := congrArg (fun x ↦ c * x * d) ih
      _ = c * (rightMulSeq (leftMulSeq c b n) d n * d) :=
        mul_assoc c (rightMulSeq (leftMulSeq c b n) d n) d
      _ = c * rightMulSeq (leftMulSeq c b n) d (n + 1) := rfl
      _ = rightMulSeq (c * leftMulSeq c b n) d (n + 1) :=
        (rightMulSeq_mul_pull d (n + 1) (leftMulSeq c b n) c).symm
      _ = rightMulSeq (leftMulSeq c b (n + 1)) d (n + 1) := rfl

/-- If `b = c * b * d` in a finite semigroup, `b` is equivalent to some left multiple sequence. -/
lemma eq_leftMulSeq_of_eq_mul_mul [Finite S] {b c d : S} (h : b = c * b * d) :
    ∃ k > 0, b = leftMulSeq c b k := by
  rcases leftMulSeq_pigeonhole c b with ⟨i, j, hij, heq⟩
  let k := j - i
  have hk_pos : 0 < k := Nat.sub_pos_of_lt hij
  have hk_eq_j : i + k = j := Nat.add_sub_of_le (le_of_lt hij)
  have h_shift : leftMulSeq c b j = leftMulSeq c (leftMulSeq c b i) k := by
    have hs : ∀ m, leftMulSeq c b (i + m) = leftMulSeq c (leftMulSeq c b i) m := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih =>
        calc leftMulSeq c b (i + m + 1) = c * leftMulSeq c b (i + m) := rfl
          _ = c * leftMulSeq c (leftMulSeq c b i) m := by rw [ih]
          _ = leftMulSeq c (leftMulSeq c b i) (m + 1) := rfl
    calc leftMulSeq c b j = leftMulSeq c b (i + k) := by rw [← hk_eq_j]
      _ = leftMulSeq c (leftMulSeq c b i) k := hs k
  have h_fi_k : leftMulSeq c (leftMulSeq c b i) k = leftMulSeq c b i := by
    rw [← h_shift, heq]
  have h_b_eq : b = rightMulSeq (leftMulSeq c b i) d i := b_eq_right_left_seq c b d h i
  have h_b_eq_k : b = leftMulSeq c b k := by
    calc b = rightMulSeq (leftMulSeq c b i) d i := h_b_eq
      _ = rightMulSeq (leftMulSeq c (leftMulSeq c b i) k) d i := by rw [h_fi_k]
      _ = leftMulSeq c (rightMulSeq (leftMulSeq c b i) d i) k :=
        (leftMulSeq_rightMulSeq_comm c (leftMulSeq c b i) d k i).symm
      _ = leftMulSeq c b k := by rw [← h_b_eq]
  exact ⟨k, hk_pos, h_b_eq_k⟩

/-- If `b = c * b * d`, then `b` is L-related to `c * b`. -/
lemma greenL_of_eq_mul_mul [Finite S] {b c d : S} (h : b = c * b * d) : IsGreenL b (c * b) := by
  obtain ⟨k, hk_pos, hk_eq⟩ := eq_leftMulSeq_of_eq_mul_mul h
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hk_pos)
  have h_cb_b : IsGreenLeftDvd (c * b) b := Or.inr ⟨c, rfl⟩
  have h_b_cb : IsGreenLeftDvd b (c * b) := by
    have h_eq_b : b = leftMulSeq c (c * b) m := by
      calc b = leftMulSeq c b (m + 1) := hk_eq
        _ = leftMulSeq c (c * b) m := leftMulSeq_pull_c c m b
    have h_left := leftMulSeq_isGreenLeftDvd c (c * b) m
    rcases h_left with h_eq_l | ⟨w, hw⟩
    · exact Or.inl (h_eq_b.trans h_eq_l)
    · exact Or.inr ⟨w, h_eq_b.trans hw⟩
  exact ⟨h_b_cb, h_cb_b⟩

open MulOpposite in
/-- If `b = c * b * d`, then `b` is R-related to `b * d`. -/
lemma greenR_of_eq_mul_mul [Finite S] {b c d : S} (h : b = c * b * d) : IsGreenR b (b * d) := by
  have hop : op b = op d * op b * op c := by
    calc op b = op (c * b * d) := congrArg op h
      _ = op d * op (c * b) := op_mul (c * b) d
      _ = op d * (op b * op c) := by rw [op_mul]
      _ = op d * op b * op c := (mul_assoc _ _ _).symm
  exact isGreenR_iff_isGreenL_op.mpr (greenL_of_eq_mul_mul hop)

/-- Green's L relation holds when a left multiplier is dropped from an already L-related element. -/
lemma isGreenL_of_isGreenL_mul {b x z : S} (h : IsGreenL b (x * (z * b))) : IsGreenL b (z * b) := by
  have h2 : IsGreenLeftDvd (z * b) b := Or.inr ⟨z, rfl⟩
  have h1 : IsGreenLeftDvd b (z * b) := by
    cases h.left with
    | inl h_eq => exact Or.inr ⟨x, h_eq⟩
    | inr h_ex =>
      rcases h_ex with ⟨w, hw⟩
      exact Or.inr ⟨w * x, by
        calc b = w * (x * (z * b)) := hw
          _ = (w * x) * (z * b) := (mul_assoc w x (z * b)).symm⟩
  exact ⟨h1, h2⟩

open MulOpposite in
/-- Green's R relation holds when a right multiplier
  is dropped from an already R-related element. -/
lemma isGreenR_of_isGreenR_mul {b u y : S} (h : IsGreenR b ((b * u) * y)) : IsGreenR b (b * u) := by
  have h2 : op ((b * u) * y) = op y * (op u * op b) := by rw [op_mul, op_mul]
  have hop : IsGreenL (op b) (op y * (op u * op b)) := by
    have h_L := isGreenR_iff_isGreenL_op.mp h
    rwa [h2] at h_L
  exact isGreenR_iff_isGreenL_op.mpr (isGreenL_of_isGreenL_mul hop)

/-- If `b = x * z * b * d`, then `b` is L-related to `z * b`. -/
lemma isGreenL_of_eq_mul_mul_mul [Finite S] {b x z d : S} (h : b = (x * z) * b * d) :
  IsGreenL b (z * b) := by
  have hl1 := greenL_of_eq_mul_mul h
  have h_assoc : (x * z) * b = x * (z * b) := mul_assoc x z b
  have hl2 : IsGreenL b (x * (z * b)) := h_assoc ▸ hl1
  exact isGreenL_of_isGreenL_mul hl2


open MulOpposite in
/-- If `b = c * b * u * y`, then `b` is R-related to `b * u`. -/
lemma isGreenR_of_eq_mul_mul_mul [Finite S] {b c u y : S} (h : b = c * b * (u * y)) :
    IsGreenR b (b * u) := by
  have hop : op b = (op y * op u) * op b * op c := by
    calc op b = op (c * b * (u * y)) := congrArg op h
      _ = op (u * y) * op (c * b) := op_mul (c * b) (u * y)
      _ = (op y * op u) * (op b * op c) := by rw [op_mul, op_mul]
      _ = (op y * op u) * op b * op c := (mul_assoc _ _ _).symm
  exact isGreenR_iff_isGreenL_op.mpr (isGreenL_of_eq_mul_mul_mul hop)

/-- If `a` is a two-sided multiple of `b`, and `b` is a two-sided multiple of `a`,
then `a` and `b` are Green's D-related. -/
lemma isGreenD_of_JRel_both [Finite S] {a b x y z u : S}
    (h1 : a = z * b * u) (h2 : b = x * a * y) : IsGreenD a b := by
  have h_b_eq : b = (x * z) * b * (u * y) := by
    calc b = x * a * y := h2
      _ = x * (z * b * u) * y := by rw [h1]
      _ = x * ((z * b) * u) * y := rfl
      _ = (x * (z * b)) * u * y := by rw [← mul_assoc x (z * b) u]
      _ = ((x * z) * b) * u * y := by rw [← mul_assoc x z b]
      _ = ((x * z) * b) * (u * y) := by rw [mul_assoc ((x * z) * b) u y]
  have hR : IsGreenR b (b * u) := isGreenR_of_eq_mul_mul_mul h_b_eq
  have hL : IsGreenL b (z * b) := isGreenL_of_eq_mul_mul_mul h_b_eq
  have hL_bu_a : IsGreenL (b * u) a := by
    have hL_bu_zbu : IsGreenL (b * u) ((z * b) * u) := IsGreenL.mul_right u hL
    exact h1.symm ▸ hL_bu_zbu
  exact ⟨b * u, IsGreenL.symm hL_bu_a, IsGreenR.symm hR⟩

/-- If `a` is a left multiple of `b` and `b` is a two-sided multiple of `a`, they are D-related. -/
lemma isGreenD_of_JRel_left_both [Finite S] {a b x y z : S}
    (h1 : a = z * b) (h2 : b = x * a * y) : IsGreenD a b := by
  have h_b_eq : b = (x * z) * b * y := by
    calc b = x * a * y := h2
      _ = x * (z * b) * y := by rw [h1]
      _ = (x * z) * b * y := by rw [← mul_assoc x z b]
  have hR : IsGreenR b (b * y) := greenR_of_eq_mul_mul h_b_eq
  have hl1 := greenL_of_eq_mul_mul h_b_eq
  have h_assoc : (x * z) * b = x * (z * b) := mul_assoc x z b
  have hL : IsGreenL b (x * (z * b)) := h_assoc ▸ hl1
  have hL2 : IsGreenL b (z * b) := isGreenL_of_isGreenL_mul hL
  have hL3 : IsGreenL b a := h1.symm ▸ hL2
  exact ⟨b, IsGreenL.symm hL3, IsGreenR.refl b⟩

/-- If `a` is a right multiple of `b` and `b` is a two-sided multiple of `a`, they are D-related. -/
lemma isGreenD_of_JRel_right_both [Finite S] {a b x y u : S}
    (h1 : a = b * u) (h2 : b = x * a * y) : IsGreenD a b := by
  have h_b_eq : b = x * b * (u * y) := by
    calc b = x * a * y := h2
      _ = x * (b * u) * y := by rw [h1]
      _ = (x * b) * u * y := by rw [← mul_assoc x b u]
      _ = x * b * (u * y) := by rw [mul_assoc (x * b) u y]
  have hr1 := greenR_of_eq_mul_mul h_b_eq
  have h_assoc : b * (u * y) = (b * u) * y := (mul_assoc b u y).symm
  have hR : IsGreenR b ((b * u) * y) := h_assoc ▸ hr1
  have hR2 : IsGreenR b (b * u) := isGreenR_of_isGreenR_mul hR
  have hR3 : IsGreenR b a := h1.symm ▸ hR2
  have hL : IsGreenL b (x * b) := greenL_of_eq_mul_mul h_b_eq
  exact ⟨a, IsGreenL.refl a, IsGreenR.symm hR3⟩

/-- If `a` is a left multiple of `b` and `b` is a right multiple of `a`, they are D-related. -/
lemma isGreenD_of_left_right [Finite S] {a b u y : S} (h1 : a = u * b) (h2 : b = a * y) :
  IsGreenD a b := by
  have h_a : a = u * a * y := by
    calc a = u * b := h1
      _ = u * (a * y) := congrArg (fun x ↦ u * x) h2
      _ = (u * a) * y := (mul_assoc u a y).symm
  have hR : IsGreenR a (a * y) := greenR_of_eq_mul_mul h_a
  have hR_ab : IsGreenR a b := h2.symm ▸ hR
  exact ⟨a, IsGreenL.refl a, hR_ab⟩

/-- If `a` is a right multiple of `b` and `b` is a left multiple of `a`, they are D-related. -/
lemma isGreenD_of_right_left [Finite S] {a b v x : S} (h1 : a = b * v) (h2 : b = x * a) :
  IsGreenD a b := by
  have h_a : a = x * a * v := by
    calc a = b * v := h1
      _ = (x * a) * v := congrArg (fun y ↦ y * v) h2
  have hL : IsGreenL a (x * a) := greenL_of_eq_mul_mul h_a
  have hL_ab : IsGreenL a b := h2.symm ▸ hL
  exact ⟨b, hL_ab, IsGreenR.refl b⟩

/-- If `a` is a left multiple of `b` and `b` is a left multiple of `a`, they are D-related. -/
lemma isGreenD_of_left_left [Finite S] {a b u x : S} (h1 : a = u * b) (h2 : b = x * a) :
  IsGreenD a b := by
  exact ⟨b, ⟨Or.inr ⟨u, h1⟩, Or.inr ⟨x, h2⟩⟩, IsGreenR.refl b⟩

/-- If `a` is a right multiple of `b` and `b` is a right multiple of `a`, they are D-related. -/
lemma isGreenD_of_right_right [Finite S] {a b v y : S} (h1 : a = b * v) (h2 : b = a * y) :
  IsGreenD a b := by
  exact ⟨a, IsGreenL.refl a, ⟨Or.inr ⟨v, h1⟩, Or.inr ⟨y, h2⟩⟩⟩

/-- A regular element `a` has an idempotent in its L-class. -/
lemma exists_idempotent_in_greenL_of_regular {S : Type*} [Semigroup S] {a : S}
    (hReg : IsGreenRegular a) : ∃ e ∈ IsGreenL.eqvClass a, e * e = e := by
  obtain ⟨s, hs⟩ := hReg
  use s * a
  constructor
  · constructor
    · right; use s
    · right; use a
      rw [← mul_assoc]
      exact hs.symm
  · have h_assoc : (s * a) * (s * a) = s * (a * s * a) := by simp [mul_assoc]
    rw [h_assoc, hs]

/-- A regular element `a` has an idempotent in its R-class. -/
lemma exists_idempotent_in_greenR_of_regular {S : Type*} [Semigroup S] {a : S}
    (hReg : IsGreenRegular a) : ∃ e ∈ IsGreenR.eqvClass a, e * e = e := by
  obtain ⟨s, hs⟩ := hReg
  use a * s
  constructor
  · constructor
    · right; use s
    · right; use a
      exact hs.symm
  · have h_assoc : (a * s) * (a * s) = (a * s * a) * s := by simp [mul_assoc]
    rw [h_assoc, hs]

/-- Two H-related idempotents must be equal. -/
lemma eq_of_isGreenH_of_idempotent {S : Type*} [Semigroup S] {a b : S}
    (hab : IsGreenH a b) (ha : a * a = a) (hb : b * b = b) : a = b := by
  have h1 : a * b = b := by
    rcases hab.right.right with rfl | ⟨x, rfl⟩ <;> simp [← mul_assoc, ha]
  have h2 : a * b = a := by
    rcases hab.left.left with rfl | ⟨y, rfl⟩ <;> simp [mul_assoc, ha, hb]
  rw [← h2, h1]

/-- If `a` is H-related to an idempotent `e`, multiplying `a` by `e` leaves `a` unchanged. -/
lemma mul_eq_self_of_isGreenH_idempotent {S : Type*} [Semigroup S] {a e : S}
    (hae : IsGreenH a e) (he : e * e = e) : a * e = a ∧ e * a = a := by
  constructor
  · rcases hae.left.left with rfl | ⟨w, rfl⟩ <;> simp [mul_assoc, he]
  · rcases hae.right.left with rfl | ⟨w, rfl⟩ <;> simp [← mul_assoc, he]

end Helpers



section GreensTheorems

/-- A D-class is regular if and only if it contains an idempotent. -/
theorem isRegularDClass_iff_exists_idempotent [Finite S]
  (D : Set S) (hD : ∃ x, D = IsGreenD.eqvClass x) :
    IsRegularDClass D ↔ ∃ e ∈ D, e * e = e := by
  obtain ⟨x₀, rfl⟩ := hD
  constructor
  · intro hReg
    have hx₀_in : x₀ ∈ IsGreenD.eqvClass x₀ := IsGreenD.refl x₀
    obtain ⟨s, hs⟩ := hReg x₀ hx₀_in
    let e := x₀ * s
    have he_idem : e * e = e := by
      dsimp [e]
      rw [← mul_assoc (x₀ * s) x₀ s, hs]
    have he_R_x₀ : IsGreenR e x₀ := by
      constructor
      · right; exact ⟨s, rfl⟩
      · right; exact ⟨x₀, hs.symm⟩
    have he_D_x₀ : IsGreenD e x₀ := ⟨e, IsGreenL.refl e, he_R_x₀⟩
    exact ⟨e, he_D_x₀, he_idem⟩
  · rintro ⟨e, heD, he_idem⟩
    intro y hyD
    have h_ye : IsGreenD y e := IsGreenD.trans hyD (IsGreenD.symm heD)
    obtain ⟨z, hL_yz, hR_ze⟩ := h_ye
    have h_ez_z : e * z = z := by
      rcases hR_ze.left with rfl | ⟨v, hv⟩
      · exact he_idem
      · rw [hv, ← mul_assoc e e v, he_idem]
    have hz_reg : ∃ u, z * u * z = z := by
      rcases hR_ze.right with rfl | ⟨u, hu⟩
      · exact ⟨e, by rw [he_idem, he_idem]⟩
      · use u
        rw [← hu, h_ez_z]
    obtain ⟨u, hu_z⟩ := hz_reg
    have hy_uz : y * u * z = y := by
      rcases hL_yz.left with rfl | ⟨p, hp⟩
      · exact hu_z
      · rw [hp, mul_assoc p z u, mul_assoc p (z * u) z, hu_z]
    rcases hL_yz.right with rfl | ⟨q, hq⟩
    · exact ⟨u, hy_uz⟩
    · use u * q
      rw [← mul_assoc y u q, mul_assoc (y * u) q y, ← hq, hy_uz]

/-- A bijection between the H-classes of two R-related elements. -/
noncomputable def equivHClassOfIsGreenR {a b : S} (h : IsGreenR a b) :
    IsGreenH.eqvClass a ≃ IsGreenH.eqvClass b := by
  by_cases hab_eq : a = b
  · exact hab_eq ▸ Equiv.refl _
  · have hex_w : ∃ w, a = b * w := h.left.resolve_left hab_eq
    let w := Classical.choose hex_w
    have hw : a = b * w := Classical.choose_spec hex_w
    have hba_neq : b ≠ a := fun heq ↦ hab_eq heq.symm
    have hex_z : ∃ z, b = a * z := h.right.resolve_left hba_neq
    let z := Classical.choose hex_z
    have hz : b = a * z := Classical.choose_spec hex_z
    have h_cancel_a : a * z * w = a := by rw [← hz, ← hw]
    have h_cancel_b : b * w * z = b := by rw [← hw, ← hz]
    refine {
      toFun := fun ⟨x, hx⟩ ↦ ⟨x * z, ?_⟩
      invFun := fun ⟨y, hy⟩ ↦ ⟨y * w, ?_⟩
      left_inv := fun ⟨x, hx⟩ ↦ Subtype.ext
        (by dsimp only; exact IsGreenL.cancellation hx.left h_cancel_a)
      right_inv := fun ⟨y, hy⟩ ↦ Subtype.ext
        (by dsimp only; exact IsGreenL.cancellation hy.left h_cancel_b)
    }
    · have hL1 : IsGreenL (x * z) (a * z) := IsGreenL.mul_right z hx.left
      have hL : IsGreenL (x * z) b := by rwa [← hz] at hL1
      have h_cancel_x : x * z * w = x := IsGreenL.cancellation hx.left h_cancel_a
      have hdvd1 : IsGreenRightDvd (x * z) x := Or.inr ⟨z, rfl⟩
      have hdvd2 : IsGreenRightDvd x (x * z) := Or.inr ⟨w, h_cancel_x.symm⟩
      have hR1 : IsGreenR (x * z) x := ⟨hdvd1, hdvd2⟩
      have hR : IsGreenR (x * z) b := IsGreenR.trans hR1 (IsGreenR.trans hx.right h)
      exact ⟨hL, hR⟩
    · have hL1 : IsGreenL (y * w) (b * w) := IsGreenL.mul_right w hy.left
      have hL : IsGreenL (y * w) a := by rwa [← hw] at hL1
      have h_cancel_y : y * w * z = y := IsGreenL.cancellation hy.left h_cancel_b
      have hdvd1 : IsGreenRightDvd (y * w) y := Or.inr ⟨w, rfl⟩
      have hdvd2 : IsGreenRightDvd y (y * w) := Or.inr ⟨z, h_cancel_y.symm⟩
      have hR1 : IsGreenR (y * w) y := ⟨hdvd1, hdvd2⟩
      have hR : IsGreenR (y * w) a := IsGreenR.trans hR1 (IsGreenR.trans hy.right (IsGreenR.symm h))
      exact ⟨hL, hR⟩

/-- A bijection between the H-classes of two L-related elements. -/
noncomputable def equivHClassOfIsGreenL {a b : S} (h : IsGreenL a b) :
    IsGreenH.eqvClass a ≃ IsGreenH.eqvClass b := by
  by_cases hab_eq : a = b
  · exact hab_eq ▸ Equiv.refl _
  · have hex_w : ∃ w, a = w * b := h.left.resolve_left hab_eq
    let w := Classical.choose hex_w
    have hw : a = w * b := Classical.choose_spec hex_w
    have hba_neq : b ≠ a := fun heq ↦ hab_eq heq.symm
    have hex_z : ∃ z, b = z * a := h.right.resolve_left hba_neq
    let z := Classical.choose hex_z
    have hz : b = z * a := Classical.choose_spec hex_z
    have h_cancel_a : w * z * a = a := by rw [mul_assoc, ← hz, ← hw]
    have h_cancel_b : z * w * b = b := by rw [mul_assoc, ← hw, ← hz]
    refine {
      toFun := fun ⟨x, hx⟩ ↦ ⟨z * x, ?_⟩
      invFun := fun ⟨y, hy⟩ ↦ ⟨w * y, ?_⟩
      left_inv := fun ⟨x, hx⟩ ↦ Subtype.ext
        (by dsimp only; rw [← mul_assoc]; exact IsGreenR.cancellation hx.right h_cancel_a)
      right_inv := fun ⟨y, hy⟩ ↦ Subtype.ext
        (by dsimp only; rw [← mul_assoc]; exact IsGreenR.cancellation hy.right h_cancel_b)
    }
    · have hR1 : IsGreenR (z * x) (z * a) := IsGreenR.mul_left z hx.right
      have hR : IsGreenR (z * x) b := by rwa [← hz] at hR1
      have h_cancel_x : w * z * x = x := IsGreenR.cancellation hx.right h_cancel_a
      have hdvd1 : IsGreenLeftDvd (z * x) x := Or.inr ⟨z, rfl⟩
      have hdvd2 : IsGreenLeftDvd x (z * x) := Or.inr ⟨w, by rw [← mul_assoc, h_cancel_x]⟩
      have hL1 : IsGreenL (z * x) x := ⟨hdvd1, hdvd2⟩
      have hL : IsGreenL (z * x) b := IsGreenL.trans hL1 (IsGreenL.trans hx.left h)
      exact ⟨hL, hR⟩
    · have hR1 : IsGreenR (w * y) (w * b) := IsGreenR.mul_left w hy.right
      have hR : IsGreenR (w * y) a := by rwa [← hw] at hR1
      have h_cancel_y : z * w * y = y := IsGreenR.cancellation hy.right h_cancel_b
      have hdvd1 : IsGreenLeftDvd (w * y) y := Or.inr ⟨w, rfl⟩
      have hdvd2 : IsGreenLeftDvd y (w * y) := Or.inr ⟨z, by rw [← mul_assoc, h_cancel_y]⟩
      have hL1 : IsGreenL (w * y) y := ⟨hdvd1, hdvd2⟩
      have hL : IsGreenL (w * y) a := IsGreenL.trans hL1 (IsGreenL.trans hy.left (IsGreenL.symm h))
      exact ⟨hL, hR⟩

open Classical in
/-- Any two H-classes within the same D-class have the same cardinality. -/
theorem card_greenHClass_eq_of_isGreenD [Fintype S] {a b : S} (h : IsGreenD a b) :
    Fintype.card (IsGreenH.eqvClass a) = Fintype.card (IsGreenH.eqvClass b) := by
  rcases h with ⟨z, hL, hR⟩
  let equiv_az := equivHClassOfIsGreenL hL
  let equiv_zb := equivHClassOfIsGreenR hR
  trans Fintype.card (IsGreenH.eqvClass z)
  · exact Fintype.card_congr equiv_az
  · exact Fintype.card_congr equiv_zb

/-- If `a` and `b` are J-related in a finite semigroup, they are also D-related. -/
lemma isGreenD_of_isGreenJ [Finite S] {a b : S} (h : IsGreenJ a b) : IsGreenD a b := by
  rcases h with ⟨hab, hba⟩
  cases hab
  case eq h1 => exact h1 ▸ IsGreenD.refl b
  case mul_left u h1 =>
    cases hba
    case eq h2 => exact h2.symm ▸ IsGreenD.refl a
    case mul_left x h2 => exact isGreenD_of_left_left h1 h2
    case mul_right y h2 => exact isGreenD_of_left_right h1 h2
    case mul_both x y h2 => exact isGreenD_of_JRel_left_both h1 h2
  case mul_right v h1 =>
    cases hba
    case eq h2 => exact h2.symm ▸ IsGreenD.refl a
    case mul_left x h2 => exact isGreenD_of_right_left h1 h2
    case mul_right y h2 => exact isGreenD_of_right_right h1 h2
    case mul_both x y h2 => exact isGreenD_of_JRel_right_both h1 h2
  case mul_both z u h1 =>
    cases hba
    case eq h2 => exact h2.symm ▸ IsGreenD.refl a
    case mul_left x h2 => exact IsGreenD.symm (isGreenD_of_JRel_left_both h2 h1)
    case mul_right y h2 => exact IsGreenD.symm (isGreenD_of_JRel_right_both h2 h1)
    case mul_both x y h2 => exact isGreenD_of_JRel_both h1 h2

/-- If `a` and `b` are D-related, they satisfy the basic J-relation step. -/
lemma isGreenJRel_of_isGreenD {a b : S} (h : IsGreenD a b) : IsGreenJRel a b := by
  rcases h with ⟨z, hL, hR⟩
  rcases hL.left with rfl | ⟨u, hu⟩
  · rcases hR.left with rfl | ⟨v, hv⟩
    · exact IsGreenJRel.eq rfl
    · exact IsGreenJRel.mul_right v hv
  · rcases hR.left with rfl | ⟨v, hv⟩
    · exact IsGreenJRel.mul_left u hu
    · exact IsGreenJRel.mul_both u v (by rw [hu, hv, mul_assoc])

/-- If `a` and `b` are D-related, they are also J-related. -/
lemma isGreenJ_of_isGreenD {a b : S} (h : IsGreenD a b) : IsGreenJ a b := by
  constructor
  · exact isGreenJRel_of_isGreenD h
  · have h_symm : IsGreenD b a := IsGreenD.symm h
    exact isGreenJRel_of_isGreenD h_symm

/-- In a finite semigroup, Green's D relation and Green's J relation are equal. -/
theorem isGreenD_eq_isGreenJ_of_finite [Finite S] : (IsGreenD : S → S → Prop) = IsGreenJ := by
  ext a b
  constructor
  · exact isGreenJ_of_isGreenD
  · exact isGreenD_of_isGreenJ

open MulOpposite in
/-- If `b` and `a * b` are D-related in a finite semigroup, they are L-related. -/
lemma isGreenL_sl_of_isGreenD_sl [Finite S] {a b : S} (h : IsGreenD b (a * b)) :
    IsGreenL b (a * b) := by
  have h_ab_dvd_b : IsGreenLeftDvd (a * b) b := Or.inr ⟨a, rfl⟩
  have h_b_dvd_ab : IsGreenLeftDvd b (a * b) := by
    rcases h with ⟨z', hL_bz', hR_z'ab⟩
    obtain ⟨z, hR_bz, hL_zab⟩ := isGreenL_commutes_isGreenR hL_bz' hR_z'ab
    have h_exists_c : ∃ c, z = c * b ∧ IsGreenLeftDvd c a := by
      rcases hL_zab.left with rfl | ⟨w, hw⟩
      · exact ⟨a, rfl, Or.inl rfl⟩
      · exact ⟨w * a, by rw [hw, ← mul_assoc], Or.inr ⟨w, rfl⟩⟩
    rcases h_exists_c with ⟨c, rfl, hc_dvd⟩
    rcases leftMulSeq_pigeonhole c b with ⟨i, j, hij, heq⟩
    have hR_all : ∀ n, IsGreenR b (leftMulSeq c b n) := by
      intro n
      induction n with
      | zero => exact IsGreenR.refl b
      | succ n ih => exact IsGreenR.trans hR_bz (IsGreenR.mul_left c ih)
    have hR_cib : IsGreenR b (leftMulSeq c b i) := hR_all i
    have h_b_eq_ckb : ∃ k > 0, b = leftMulSeq c b k := by
      let k := j - i
      have hk_pos : 0 < k := Nat.sub_pos_of_lt hij
      have hk_eq_j : i + k = j := Nat.add_sub_of_le (le_of_lt hij)
      have h_shift : leftMulSeq c b j = leftMulSeq c (leftMulSeq c b i) k := by
        have hs : ∀ m, leftMulSeq c b (i + m) = leftMulSeq c (leftMulSeq c b i) m := by
          intro m
          induction m with
          | zero => rfl
          | succ m ih =>
            calc leftMulSeq c b (i + m + 1) = c * leftMulSeq c b (i + m) := rfl
              _ = c * leftMulSeq c (leftMulSeq c b i) m := by rw [ih]
              _ = leftMulSeq c (leftMulSeq c b i) (m + 1) := rfl
        calc leftMulSeq c b j = leftMulSeq c b (i + k) := by rw [← hk_eq_j]
          _ = leftMulSeq c (leftMulSeq c b i) k := hs k
      have h_gi_k : leftMulSeq c (leftMulSeq c b i) k = leftMulSeq c b i := by
        rw [← h_shift, heq]
      use k, hk_pos
      rcases hR_cib.left with heq_b | ⟨v_outer, hv⟩
      · calc b = leftMulSeq c b i := heq_b
          _ = leftMulSeq c (leftMulSeq c b i) k := h_gi_k.symm
          _ = leftMulSeq c b k := by rw [← heq_b]
      · calc b = leftMulSeq c b i * v_outer := hv
          _ = leftMulSeq c (leftMulSeq c b i) k * v_outer := by rw [h_gi_k]
          _ = leftMulSeq c (leftMulSeq c b i * v_outer) k :=
            (leftMulSeq_mul_pull c k _ v_outer).symm
          _ = leftMulSeq c b k := by rw [← hv]
    rcases h_b_eq_ckb with ⟨k, hk_pos, hk_eq⟩
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hk_pos)
    rcases hc_dvd with hc_eq_a | ⟨w, hw⟩
    · rcases m with _ | m_pred
      · have h_final : b = a * b := by
          calc b = leftMulSeq c b (0 + 1) := hk_eq
            _ = leftMulSeq c (c * b) 0 := leftMulSeq_pull_c c 0 b
            _ = leftMulSeq c (a * b) 0 := congrArg (fun x ↦ leftMulSeq c (x * b) 0) hc_eq_a
            _ = a * b := rfl
        exact Or.inl h_final
      · have h_final : b = leftMulSeq c c m_pred * (a * b) := by
          calc b = leftMulSeq c b (m_pred + 1 + 1) := hk_eq
            _ = leftMulSeq c (c * b) (m_pred + 1) := leftMulSeq_pull_c c (m_pred + 1) b
            _ = leftMulSeq c (a * b) (m_pred + 1) :=
              congrArg (fun x ↦ leftMulSeq c (x * b) (m_pred + 1)) hc_eq_a
            _ = leftMulSeq c (c * (a * b)) m_pred := leftMulSeq_pull_c c m_pred (a * b)
            _ = leftMulSeq c c m_pred * (a * b) := leftMulSeq_mul_pull c m_pred c (a * b)
        exact Or.inr ⟨leftMulSeq c c m_pred, h_final⟩
    · have h_final : b = leftMulSeq c w m * (a * b) := by
        calc b = leftMulSeq c b (m + 1) := hk_eq
          _ = leftMulSeq c (c * b) m := leftMulSeq_pull_c c m b
          _ = leftMulSeq c ((w * a) * b) m := congrArg (fun x ↦ leftMulSeq c (x * b) m) hw
          _ = leftMulSeq c (w * (a * b)) m := congrArg (leftMulSeq c · m) (mul_assoc w a b)
          _ = leftMulSeq c w m * (a * b) := leftMulSeq_mul_pull c m w (a * b)
      exact Or.inr ⟨leftMulSeq c w m, h_final⟩
  exact ⟨h_b_dvd_ab, h_ab_dvd_b⟩

open MulOpposite in
/-- If `a` and `a * b` are D-related in a finite semigroup, they are R-related. -/
lemma isGreenR_sr_of_isGreenD_sr [Finite S] {a b : S} (h : IsGreenD a (a * b)) :
    IsGreenR a (a * b) := by
  have hop : IsGreenD (op a) (op b * op a) := by
    have hd := IsGreenD.isGreenD_iff_isGreenD_op.mp h
    rwa [op_mul] at hd
  exact isGreenR_iff_isGreenL_op.mpr (isGreenL_sl_of_isGreenD_sl hop)

/-- If `a, b`, and `a * b` are all in the same regular D-class, then `a R a * b`, `b L a * b`,
and there exists an idempotent `e` in the D-class such that `a L e` and `b R e`. -/
theorem mul_mem_isGreenD_eqvClass_properties
  [Finite S] {D : Set S} (hD : ∃ x, D = IsGreenD.eqvClass x)
    (a b : S) (ha : a ∈ D) (hb : b ∈ D) (hab : a * b ∈ D) :
    (IsGreenR a (a * b) ∧ IsGreenL b (a * b)) ∧
    (∃ e ∈ D, e * e = e ∧ IsGreenL a e ∧ IsGreenR b e) := by
  obtain ⟨x0, hx0⟩ := hD
  have hDa : IsGreenD a x0 := by have h := ha; rw [hx0] at h; exact h
  have hDb : IsGreenD b x0 := by have h := hb; rw [hx0] at h; exact h
  have hDab : IsGreenD (a * b) x0 := by have h := hab; rw [hx0] at h; exact h
  have h_a_D_ab : IsGreenD a (a * b) := IsGreenD.trans hDa (IsGreenD.symm hDab)
  have h_b_D_ab : IsGreenD b (a * b) := IsGreenD.trans hDb (IsGreenD.symm hDab)
  have hR_a_ab : IsGreenR a (a * b) := isGreenR_sr_of_isGreenD_sr h_a_D_ab
  have hL_b_ab : IsGreenL b (a * b) := isGreenL_sl_of_isGreenD_sl h_b_D_ab
  refine ⟨⟨hR_a_ab, hL_b_ab⟩, ?_⟩
  have h_a_dvd : IsGreenRightDvd a (a * b) := hR_a_ab.left
  have h_b_dvd : IsGreenLeftDvd b (a * b) := hL_b_ab.left
  rcases h_a_dvd with h_a_eq | ⟨u, hu⟩
  · rcases h_b_dvd with h_b_eq | ⟨v, hv⟩
    · use a
      have hab_eq : a = b := h_a_eq.trans h_b_eq.symm
      have idem : a * a = a := by
        calc a * a = a * b := congrArg (fun x ↦ a * x) hab_eq
             _     = a     := h_a_eq.symm
      refine ⟨ha, idem, IsGreenL.refl a, ?_⟩
      exact hab_eq ▸ IsGreenR.refl b
    · use b
      have h1 : v * a = b := by
        calc v * a = v * (a * b) := congrArg (fun x ↦ v * x) h_a_eq
             _     = b           := hv.symm
      have idem : b * b = b := by
        calc b * b = (v * a) * b := congrArg (fun x ↦ x * b) h1.symm
             _     = v * (a * b) := mul_assoc v a b
             _     = b           := hv.symm
      have hLab : IsGreenL a b := ⟨Or.inr ⟨a, h_a_eq⟩, Or.inr ⟨v, h1.symm⟩⟩
      exact ⟨hb, idem, hLab, IsGreenR.refl b⟩
  · rcases h_b_dvd with h_b_eq | ⟨v, hv⟩
    · use a
      have h2 : b * u = a := by
        calc b * u = (a * b) * u := congrArg (fun x ↦ x * u) h_b_eq
             _     = a           := hu.symm
      have idem : a * a = a := by
        calc a * a = a * (b * u) := congrArg (fun x ↦ a * x) h2.symm
             _     = (a * b) * u := (mul_assoc a b u).symm
             _     = a           := hu.symm
      have hRba : IsGreenR b a := ⟨Or.inr ⟨b, h_b_eq⟩, Or.inr ⟨u, h2.symm⟩⟩
      exact ⟨ha, idem, IsGreenL.refl a, hRba⟩
    · use v * a
      have he_eq : v * a = b * u := by
        calc v * a = v * (a * b * u)   := congrArg (fun x ↦ v * x) hu
             _     = (v * (a * b)) * u := (mul_assoc v (a * b) u).symm
             _     = b * u             := congrArg (fun x ↦ x * u) hv.symm
      have idem : (v * a) * (v * a) = v * a := by
        calc (v * a) * (v * a) = (v * a) * (b * u) := congrArg (fun x ↦ (v * a) * x) he_eq
             _ = v * (a * (b * u))                 := mul_assoc v a (b * u)
             _ = v * (a * b * u)                   :=
              congrArg (fun x ↦ v * x) (mul_assoc a b u).symm
             _ = v * a                             := congrArg (fun x ↦ v * x) hu.symm
      have hLae1 : a = a * (v * a) := by
        calc a = a * b * u   := hu
             _ = a * (b * u) := mul_assoc a b u
             _ = a * (v * a) := congrArg (fun x ↦ a * x) he_eq.symm
      have hLae : IsGreenL a (v * a) := ⟨Or.inr ⟨a, hLae1⟩, Or.inr ⟨v, rfl⟩⟩
      have hRbe1 : b = (v * a) * b := by
        calc b = v * (a * b) := hv
             _ = (v * a) * b := (mul_assoc v a b).symm
      have hRbe : IsGreenR b (v * a) := ⟨Or.inr ⟨b, hRbe1⟩, Or.inr ⟨u, he_eq⟩⟩
      have heD : v * a ∈ D := by
        have hDea : IsGreenD (v * a) a := ⟨a, IsGreenL.symm hLae, IsGreenR.refl a⟩
        have he_D : IsGreenD (v * a) x0 := IsGreenD.trans hDea hDa
        rw [hx0]
        exact he_D
      exact ⟨heD, idem, hLae, hRbe⟩

/-- An H-class is either a group or contains no idempotents
  and is not closed under multiplication. -/
lemma isGroup_isGreenH_eqvClass_iff_idempotent
    [Finite S] (H : Set S) (hH : ∃ a, H = IsGreenH.eqvClass a) :
    (∀ x y, x ∈ H → y ∈ H → x * y ∉ H) ∨
    (∃ e ∈ H, e * e = e ∧ ∀ x y, x ∈ H → y ∈ H → x * y ∈ H) := by
  obtain ⟨a, rfl⟩ := hH
  by_cases h : ∀ x y, x ∈ IsGreenH.eqvClass a → y ∈ IsGreenH.eqvClass a →
    x * y ∉ IsGreenH.eqvClass a
  · exact Or.inl h
  · right
    push_neg at h
    obtain ⟨x₀, y₀, hx₀, hy₀, hxy₀⟩ := h
    have hx₀H : IsGreenH x₀ a := hx₀
    have hy₀H : IsGreenH y₀ a := hy₀
    have hxy₀H : IsGreenH (x₀ * y₀) a := hxy₀
    have hx₀D : x₀ ∈ IsGreenD.eqvClass a := by
      simp only [IsGreenD.eqvClass, Set.mem_setOf_eq]
      exact ⟨a, hx₀H.left, IsGreenR.refl a⟩
    have hy₀D : y₀ ∈ IsGreenD.eqvClass a := by
      simp only [IsGreenD.eqvClass, Set.mem_setOf_eq]
      exact ⟨a, hy₀H.left, IsGreenR.refl a⟩
    have hxy₀D : x₀ * y₀ ∈ IsGreenD.eqvClass a := by
      simp only [IsGreenD.eqvClass, Set.mem_setOf_eq]
      exact ⟨a, hxy₀H.left, IsGreenR.refl a⟩
    obtain ⟨_, e, heD, he_idem, hLx₀e, hRy₀e⟩ :=
      mul_mem_isGreenD_eqvClass_properties (D := IsGreenD.eqvClass a) ⟨a, rfl⟩ x₀ y₀ hx₀D hy₀D hxy₀D
    have hLx₀a : IsGreenL x₀ a := hx₀H.left
    have hRy₀a : IsGreenR y₀ a := hy₀H.right
    have hLae : IsGreenL a e := IsGreenL.trans (IsGreenL.symm hLx₀a) hLx₀e
    have hRae : IsGreenR a e := IsGreenR.trans (IsGreenR.symm hRy₀a) hRy₀e
    have heH : e ∈ IsGreenH.eqvClass a := ⟨IsGreenL.symm hLae, IsGreenR.symm hRae⟩
    refine ⟨e, heH, he_idem, ?_⟩
    intro u v huH hvH
    have hue : IsGreenH u e := IsGreenH.trans huH (IsGreenH.symm heH)
    have hve : IsGreenH v e := IsGreenH.trans hvH (IsGreenH.symm heH)
    have hLue : IsGreenL u e := hue.left
    have hRve : IsGreenR v e := hve.right
    have hev : e * v = v := by
      rcases hRve.left with rfl | ⟨z, hz⟩
      · exact he_idem
      · rw [hz, ← mul_assoc, he_idem]
    have hue_eq : u * e = u := by
      rcases hLue.left with rfl | ⟨w, hw⟩
      · exact he_idem
      · rw [hw, mul_assoc, he_idem]
    have hLuv_ev : IsGreenL (u * v) (e * v) := IsGreenL.mul_right v hLue
    have hLuv_v : IsGreenL (u * v) v := by rwa [hev] at hLuv_ev
    have hRuv_ue : IsGreenR (u * v) (u * e) := IsGreenR.mul_left u hRve
    have hRuv_u : IsGreenR (u * v) u := by rwa [hue_eq] at hRuv_ue
    have hLuv_a : IsGreenL (u * v) a := IsGreenL.trans hLuv_v hvH.left
    have hRuv_a : IsGreenR (u * v) a := IsGreenR.trans hRuv_u huH.right
    exact ⟨hLuv_a, hRuv_a⟩

end GreensTheorems
