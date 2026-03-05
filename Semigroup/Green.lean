import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Green's Relations
-/

variable {S : Type*} [Semigroup S]

section GreenDefinitions

def IsGreenLeftDvd (a b : S) : Prop := a = b ∨ ∃ z, a = z * b
def IsGreenRightDvd (a b : S) : Prop := a = b ∨ ∃ z, a = b * z

inductive IsGreenJRel (a b : S) : Prop
  | eq (h : a = b)
  | mul_left (u : S) (h : a = u * b)
  | mul_right (v : S) (h : a = b * v)
  | mul_both (u v : S) (h : a = u * b * v)

def IsGreenL (a b : S) : Prop := IsGreenLeftDvd a b ∧ IsGreenLeftDvd b a
def IsGreenR (a b : S) : Prop := IsGreenRightDvd a b ∧ IsGreenRightDvd b a
def IsGreenH (a b : S) : Prop := IsGreenL a b ∧ IsGreenR a b
def IsGreenD (a b : S) : Prop := ∃ z, IsGreenL a z ∧ IsGreenR z b
def IsGreenJ (a b : S) : Prop := IsGreenJRel a b ∧ IsGreenJRel b a

end GreenDefinitions


section GreenEquivalences

namespace IsGreenLeftDvd

@[refl] theorem refl (a : S) : IsGreenLeftDvd a a := Or.inl rfl

@[trans] theorem trans {a b c : S} (hab : IsGreenLeftDvd a b)
  (hbc : IsGreenLeftDvd b c) : IsGreenLeftDvd a c := by
  rcases hab with rfl | ⟨x, hx⟩
  · exact hbc
  · rcases hbc with rfl | ⟨y, hy⟩
    · exact Or.inr ⟨x, hx⟩
    · exact Or.inr ⟨x * y, by rw [hx, hy, mul_assoc]⟩

end IsGreenLeftDvd


namespace IsGreenRightDvd

@[refl] theorem refl (a : S) : IsGreenRightDvd a a := Or.inl rfl

@[trans] theorem trans {a b c : S} (hab : IsGreenRightDvd a b)
  (hbc : IsGreenRightDvd b c) : IsGreenRightDvd a c := by
  rcases hab with rfl | ⟨x, hx⟩
  · exact hbc
  · rcases hbc with rfl | ⟨y, hy⟩
    · exact Or.inr ⟨x, hx⟩
    · exact Or.inr ⟨y * x, by rw [hx, hy, mul_assoc]⟩

end IsGreenRightDvd


namespace IsGreenJRel

@[refl] theorem refl (a : S) : IsGreenJRel a a := eq rfl

@[trans] theorem trans {a b c : S} (hab : IsGreenJRel a b)
  (hbc : IsGreenJRel b c) : IsGreenJRel a c := by
  cases hab
  case eq h => subst h; exact hbc
  case mul_left u1 h1 =>
    cases hbc
    case eq h2 => subst h2; exact mul_left u1 h1
    case mul_left u2 h2 => exact mul_left (u1 * u2) (by simp [h1, h2, mul_assoc])
    case mul_right v2 h2 => exact mul_both u1 v2 (by simp [h1, h2, mul_assoc])
    case mul_both u2 v2 h2 => exact mul_both (u1 * u2) v2 (by simp [h1, h2, mul_assoc])
  case mul_right v1 h1 =>
    cases hbc
    case eq h2 => subst h2; exact mul_right v1 h1
    case mul_left u2 h2 => exact mul_both u2 v1 (by simp [h1, h2, mul_assoc])
    case mul_right v2 h2 => exact mul_right (v2 * v1) (by simp [h1, h2, mul_assoc])
    case mul_both u2 v2 h2 => exact mul_both u2 (v2 * v1) (by simp [h1, h2, mul_assoc])
  case mul_both u1 v1 h1 =>
    cases hbc
    case eq h2 => subst h2; exact mul_both u1 v1 h1
    case mul_left u2 h2 => exact mul_both (u1 * u2) v1 (by simp [h1, h2, mul_assoc])
    case mul_right v2 h2 => exact mul_both u1 (v2 * v1) (by simp [h1, h2, mul_assoc])
    case mul_both u2 v2 h2 => exact mul_both (u1 * u2) (v2 * v1) (by simp [h1, h2, mul_assoc])

end IsGreenJRel


namespace IsGreenL

@[refl] theorem refl (a : S) : IsGreenL a a :=
  ⟨IsGreenLeftDvd.refl a, IsGreenLeftDvd.refl a⟩

@[symm] theorem symm {a b : S} (h : IsGreenL a b) : IsGreenL b a :=
  ⟨h.right, h.left⟩

@[trans] theorem trans {a b c : S} (hab : IsGreenL a b) (hbc : IsGreenL b c) : IsGreenL a c :=
  ⟨IsGreenLeftDvd.trans hab.left hbc.left, IsGreenLeftDvd.trans hbc.right hab.right⟩

protected def setoid (S : Type*) [Semigroup S] : Setoid S where
  r := IsGreenL
  iseqv := {
    refl := refl
    symm := symm
    trans := trans
  }

theorem mul_right (c : S) {a b : S} (h : IsGreenL a b) : IsGreenL (a * c) (b * c) := by
  rcases h with ⟨h1, h2⟩
  constructor
  · rcases h1 with rfl | ⟨z, hz⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨z, by rw [hz, mul_assoc]⟩
  · rcases h2 with rfl | ⟨z, hz⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨z, by rw [hz, mul_assoc]⟩

theorem cancellation {a x u v : S} (hx : IsGreenL x a) (h_cancel : a * u * v = a) :
    x * u * v = x := by
  rcases hx.left with rfl | ⟨k, rfl⟩
  · exact h_cancel
  · simp only [mul_assoc, h_cancel]

end IsGreenL


namespace IsGreenR

@[refl] theorem refl (a : S) : IsGreenR a a :=
  ⟨IsGreenRightDvd.refl a, IsGreenRightDvd.refl a⟩

@[symm] theorem symm {a b : S} (h : IsGreenR a b) : IsGreenR b a :=
  ⟨h.right, h.left⟩

@[trans] theorem trans {a b c : S} (hab : IsGreenR a b) (hbc : IsGreenR b c) : IsGreenR a c :=
  ⟨IsGreenRightDvd.trans hab.left hbc.left, IsGreenRightDvd.trans hbc.right hab.right⟩

protected def setoid (S : Type*) [Semigroup S] : Setoid S where
  r := IsGreenR
  iseqv := {
    refl := refl
    symm := symm
    trans := trans
  }

theorem mul_left (c : S) {a b : S} (h : IsGreenR a b) : IsGreenR (c * a) (c * b) := by
  rcases h with ⟨h1, h2⟩
  constructor
  · rcases h1 with rfl | ⟨z, hz⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨z, by rw [hz, ← mul_assoc]⟩
  · rcases h2 with rfl | ⟨z, hz⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨z, by rw [hz, ← mul_assoc]⟩

theorem cancellation {a x u v : S} (hx : IsGreenR x a) (h_cancel : v * u * a = a) :
    v * u * x = x := by
  rcases hx.left with rfl | ⟨k, rfl⟩
  · exact h_cancel
  · simp only [← mul_assoc, h_cancel]

end IsGreenR


namespace IsGreenH

@[refl] theorem refl (a : S) : IsGreenH a a :=
  ⟨IsGreenL.refl a, IsGreenR.refl a⟩

@[symm] theorem symm {a b : S} (h : IsGreenH a b) : IsGreenH b a :=
  ⟨IsGreenL.symm h.left, IsGreenR.symm h.right⟩

@[trans] theorem trans {a b c : S} (hab : IsGreenH a b) (hbc : IsGreenH b c) : IsGreenH a c :=
  ⟨IsGreenL.trans hab.left hbc.left, IsGreenR.trans hab.right hbc.right⟩

protected def setoid (S : Type*) [Semigroup S] : Setoid S where
  r := IsGreenH
  iseqv := {
    refl := refl
    symm := symm
    trans := trans
  }

end IsGreenH


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

@[refl] theorem refl (a : S) : IsGreenD a a :=
  ⟨a, IsGreenL.refl a, IsGreenR.refl a⟩

@[symm] theorem symm {a b : S} (h : IsGreenD a b) : IsGreenD b a := by
  obtain ⟨z, hL, hR⟩ := h
  obtain ⟨z', h_x_R_z', h_z'_L_y⟩ := isGreenL_commutes_isGreenR hL hR
  exact ⟨z', IsGreenL.symm h_z'_L_y, IsGreenR.symm h_x_R_z'⟩

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

protected def setoid (S : Type*) [Semigroup S] : Setoid S where
  r := IsGreenD
  iseqv := {
    refl := refl
    symm := symm
    trans := trans
  }

end IsGreenD


namespace IsGreenJ

@[refl] theorem refl (a : S) : IsGreenJ a a :=
  ⟨IsGreenJRel.refl a, IsGreenJRel.refl a⟩

@[symm] theorem symm {a b : S} (h : IsGreenJ a b) : IsGreenJ b a :=
  ⟨h.right, h.left⟩

@[trans] theorem trans {a b c : S} (hab : IsGreenJ a b) (hbc : IsGreenJ b c) : IsGreenJ a c :=
  ⟨IsGreenJRel.trans hab.left hbc.left, IsGreenJRel.trans hbc.right hab.right⟩

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
def eqvClass (x : S) : Set S := setOf (IsGreenL · x)
end IsGreenL

namespace IsGreenR
def eqvClass (x : S) : Set S := setOf (IsGreenR · x)
end IsGreenR

namespace IsGreenH
def eqvClass (x : S) : Set S := setOf (IsGreenH · x)
end IsGreenH

namespace IsGreenD
def eqvClass (x : S) : Set S := setOf (IsGreenD · x)
end IsGreenD

namespace IsGreenJ
def eqvClass (x : S) : Set S := setOf (IsGreenJ · x)
end IsGreenJ

def GreenLClass (S : Type*) [Semigroup S] := Quotient (IsGreenL.setoid S)

namespace GreenLClass
def mk (x : S) : GreenLClass S := Quotient.mk (IsGreenL.setoid S) x
end GreenLClass

def GreenRClass (S : Type*) [Semigroup S] := Quotient (IsGreenR.setoid S)

namespace GreenRClass
def mk (x : S) : GreenRClass S := Quotient.mk (IsGreenR.setoid S) x
end GreenRClass

def GreenHClass (S : Type*) [Semigroup S] := Quotient (IsGreenH.setoid S)

namespace GreenHClass
def mk (x : S) : GreenHClass S := Quotient.mk (IsGreenH.setoid S) x
end GreenHClass

def GreenDClass (S : Type*) [Semigroup S] := Quotient (IsGreenD.setoid S)

namespace GreenDClass
def mk (x : S) : GreenDClass S := Quotient.mk (IsGreenD.setoid S) x
end GreenDClass

def GreenJClass (S : Type*) [Semigroup S] := Quotient (IsGreenJ.setoid S)

namespace GreenJClass
def mk (x : S) : GreenJClass S := Quotient.mk (IsGreenJ.setoid S) x
end GreenJClass

def IsGreenRegular (a : S) : Prop := ∃ s, a * s * a = a

def IsRegularDClass (D : Set S) : Prop := ∀ x ∈ D, IsGreenRegular x

end GreenClasses



section GreensFacts

-- Fact 2.3
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


noncomputable def equivHClassOfIsGreenR {a b : S} (h : IsGreenR a b) :
    IsGreenH.eqvClass a ≃ IsGreenH.eqvClass b := by
  by_cases hab_eq : a = b
  · subst hab_eq; exact Equiv.refl _
  · have hex_w : ∃ w, a = b * w := h.left.resolve_left hab_eq
    let w := Classical.choose hex_w
    have hw : a = b * w := Classical.choose_spec hex_w
    have hba_neq : b ≠ a := fun heq => hab_eq heq.symm
    have hex_z : ∃ z, b = a * z := h.right.resolve_left hba_neq
    let z := Classical.choose hex_z
    have hz : b = a * z := Classical.choose_spec hex_z
    have h_cancel_a : a * z * w = a := by rw [← hz, ← hw]
    have h_cancel_b : b * w * z = b := by rw [← hw, ← hz]
    refine {
      toFun := fun ⟨x, hx⟩ => ⟨x * z, ?_⟩
      invFun := fun ⟨y, hy⟩ => ⟨y * w, ?_⟩
      left_inv := fun ⟨x, hx⟩ => Subtype.ext
        (by dsimp only; exact IsGreenL.cancellation hx.left h_cancel_a)
      right_inv := fun ⟨y, hy⟩ => Subtype.ext
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

noncomputable def equivHClassOfIsGreenL {a b : S} (h : IsGreenL a b) :
    IsGreenH.eqvClass a ≃ IsGreenH.eqvClass b := by
  by_cases hab_eq : a = b
  · subst hab_eq; exact Equiv.refl _
  · have hex_w : ∃ w, a = w * b := h.left.resolve_left hab_eq
    let w := Classical.choose hex_w
    have hw : a = w * b := Classical.choose_spec hex_w
    have hba_neq : b ≠ a := fun heq => hab_eq heq.symm
    have hex_z : ∃ z, b = z * a := h.right.resolve_left hba_neq
    let z := Classical.choose hex_z
    have hz : b = z * a := Classical.choose_spec hex_z
    have h_cancel_a : w * z * a = a := by rw [mul_assoc, ← hz, ← hw]
    have h_cancel_b : z * w * b = b := by rw [mul_assoc, ← hw, ← hz]
    refine {
      toFun := fun ⟨x, hx⟩ => ⟨z * x, ?_⟩
      invFun := fun ⟨y, hy⟩ => ⟨w * y, ?_⟩
      left_inv := fun ⟨x, hx⟩ => Subtype.ext
        (by dsimp only; rw [← mul_assoc]; exact IsGreenR.cancellation hx.right h_cancel_a)
      right_inv := fun ⟨y, hy⟩ => Subtype.ext
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

-- Fact 2.5
open Classical in
theorem card_greenHClass_eq_of_isGreenD [Fintype S] {a b : S} (h : IsGreenD a b) :
    Fintype.card (IsGreenH.eqvClass a) = Fintype.card (IsGreenH.eqvClass b) := by
  rcases h with ⟨z, hL, hR⟩
  let equiv_az := equivHClassOfIsGreenL hL
  let equiv_zb := equivHClassOfIsGreenR hR
  trans Fintype.card (IsGreenH.eqvClass z)
  · exact Fintype.card_congr equiv_az
  · exact Fintype.card_congr equiv_zb



lemma isGreenD_of_isGreenJ [Finite S] {a b : S} (h : IsGreenJ a b) : IsGreenD a b := by
  sorry

lemma isGreenJRel_of_isGreenD {a b : S} (h : IsGreenD a b) : IsGreenJRel a b := by
  rcases h with ⟨z, hL, hR⟩
  rcases hL.left with rfl | ⟨u, hu⟩
  · rcases hR.left with rfl | ⟨v, hv⟩
    · exact IsGreenJRel.eq rfl
    · exact IsGreenJRel.mul_right v hv
  · rcases hR.left with rfl | ⟨v, hv⟩
    · exact IsGreenJRel.mul_left u hu
    · exact IsGreenJRel.mul_both u v (by rw [hu, hv, mul_assoc])


lemma isGreenJ_of_isGreenD {a b : S} (h : IsGreenD a b) : IsGreenJ a b := by
  constructor
  · exact isGreenJRel_of_isGreenD h
  · have h_symm : IsGreenD b a := IsGreenD.symm h
    exact isGreenJRel_of_isGreenD h_symm

-- Fact 2.2
theorem isGreenD_eq_isGreenJ_of_finite [Finite S] : (IsGreenD : S → S → Prop) = IsGreenJ := by
  ext a b
  constructor
  · exact isGreenJ_of_isGreenD
  · exact isGreenD_of_isGreenJ


lemma isGreenR_sr_of_isGreenD_sr [Finite S] {a b : S} (h : IsGreenD a (a * b)) :
    IsGreenR a (a * b) := by
  have h_ab_dvd_a : IsGreenRightDvd (a * b) a := Or.inr ⟨b, rfl⟩
  have h_a_dvd_ab : IsGreenRightDvd a (a * b) := by
    rcases h with ⟨z, hL_az, hR_zab⟩

    have h_exists_c : ∃ c, z = a * c ∧ IsGreenRightDvd c b := by
      rcases hR_zab.left with rfl | ⟨w, hw⟩
      · exact ⟨b, rfl, Or.inl rfl⟩
      · exact ⟨b * w, by rw [hw, mul_assoc], Or.inr ⟨w, rfl⟩⟩
    rcases h_exists_c with ⟨c, rfl, hc_dvd⟩

    let R : ℕ → S → S := fun n x => Nat.recOn (motive := fun _ => S) n x (fun _ acc => acc * c)

    have h_mul_pull : ∀ m x u, R m (u * x) = u * R m x := by
      intro m x u
      induction m with
      | zero => rfl
      | succ m ih =>
        calc R (m + 1) (u * x) = R m (u * x) * c := rfl
          _ = (u * R m x) * c := by rw [ih]
          _ = u * (R m x * c) := mul_assoc u (R m x) c
          _ = u * R (m + 1) x := rfl

    let f : ℕ → S := fun n => R n a

    have h_pigeonhole : ∃ i j : ℕ, i < j ∧ f i = f j := by
      obtain ⟨i, j, h_neq, heq⟩ := Finite.exists_ne_map_eq_of_infinite f
      rcases lt_trichotomy i j with h_lt | h_eq | h_gt
      · exact ⟨i, j, h_lt, heq⟩
      · exact False.elim (h_neq h_eq)
      · exact ⟨j, i, h_gt, heq.symm⟩

    rcases h_pigeonhole with ⟨i, j, hij, heq⟩

    have hL_all : ∀ n, IsGreenL a (f n) := by
      intro n
      induction n with
      | zero => exact IsGreenL.refl a
      | succ n ih => exact IsGreenL.trans hL_az (IsGreenL.mul_right c ih)
    have hL_aci : IsGreenL a (f i) := hL_all i

    have h_a_eq_ack : ∃ k > 0, a = R k a := by
      let k := j - i
      have hk_pos : 0 < k := Nat.sub_pos_of_lt hij
      have hk_eq_j : i + k = j := Nat.add_sub_of_le (le_of_lt hij)
      have h_shift : ∀ m, f (i + m) = R m (f i) := by
        intro m
        induction m with
        | zero => rfl
        | succ m ih =>
          calc f (i + (m + 1)) = f (i + m + 1) := rfl
            _ = f (i + m) * c := rfl
            _ = R m (f i) * c := by rw [ih]
            _ = R (m + 1) (f i) := rfl
      have h_fi_k : R k (f i) = f i := by
        calc R k (f i) = f (i + k) := (h_shift k).symm
          _ = f j := by rw [hk_eq_j]
          _ = f i := heq.symm
      use k, hk_pos
      rcases hL_aci.left with heq_a | ⟨u, hu⟩
      · calc a = f i := heq_a
          _ = R k (f i) := h_fi_k.symm
          _ = R k a := by rw [heq_a]
      · calc a = u * f i := hu
          _ = u * R k (f i) := by rw [h_fi_k]
          _ = R k (u * f i) := (h_mul_pull k (f i) u).symm
          _ = R k a := by rw [← hu]

    rcases h_a_eq_ack with ⟨k, hk_pos, hk_eq⟩

    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hk_pos)

    have h_pull_c : ∀ n x, R (n + 1) x = R n (x * c) := by
      intro n x
      induction n with
      | zero => rfl
      | succ n ih =>
        calc R (n + 1 + 1) x = R (n + 1) x * c := rfl
          _ = R n (x * c) * c := by rw [ih]
          _ = R (n + 1) (x * c) := rfl

    rcases hc_dvd with hc_eq_b | ⟨w, hw⟩
    · rcases m with _ | m_pred
      · have h_final : a = a * b := by
          calc a = R (0 + 1) a := hk_eq
            _ = R 0 (a * c) := h_pull_c 0 a
            _ = R 0 (a * b) := congrArg (fun x => R 0 (a * x)) hc_eq_b
            _ = a * b := rfl
        exact Or.inl h_final
      · have h_final : a = (a * b) * R m_pred c := by
          calc a = R (m_pred + 1 + 1) a := hk_eq
            _ = R (m_pred + 1) (a * c) := h_pull_c (m_pred + 1) a
            _ = R (m_pred + 1) (a * b) := congrArg (fun x => R (m_pred + 1) (a * x)) hc_eq_b
            _ = R m_pred ((a * b) * c) := h_pull_c m_pred (a * b)
            _ = (a * b) * R m_pred c := h_mul_pull m_pred c (a * b)
        exact Or.inr ⟨R m_pred c, h_final⟩
    · have h_final : a = (a * b) * R m w := by
        calc a = R (m + 1) a := hk_eq
          _ = R m (a * c) := h_pull_c m a
          _ = R m (a * (b * w)) := congrArg (fun x => R m (a * x)) hw
          _ = R m ((a * b) * w) := congrArg (R m) (mul_assoc a b w).symm
          _ = (a * b) * R m w := h_mul_pull m w (a * b)
      exact Or.inr ⟨R m w, h_final⟩

  exact ⟨h_a_dvd_ab, h_ab_dvd_a⟩

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

    let L : ℕ → S → S := fun n x => Nat.recOn (motive := fun _ => S) n x (fun _ acc => c * acc)

    have h_mul_pull : ∀ m x v, L m (x * v) = L m x * v := by
      intro m x v
      induction m with
      | zero => rfl
      | succ m ih =>
        calc L (m + 1) (x * v) = c * L m (x * v) := rfl
          _ = c * (L m x * v) := by rw [ih]
          _ = (c * L m x) * v := (mul_assoc c (L m x) v).symm
          _ = L (m + 1) x * v := rfl

    let g : ℕ → S := fun n => L n b

    have h_pigeonhole : ∃ i j : ℕ, i < j ∧ g i = g j := by
      obtain ⟨i, j, h_neq, heq⟩ := Finite.exists_ne_map_eq_of_infinite g
      rcases lt_trichotomy i j with h_lt | h_eq | h_gt
      · exact ⟨i, j, h_lt, heq⟩
      · exact False.elim (h_neq h_eq)
      · exact ⟨j, i, h_gt, heq.symm⟩

    rcases h_pigeonhole with ⟨i, j, hij, heq⟩

    have hR_all : ∀ n, IsGreenR b (g n) := by
      intro n
      induction n with
      | zero => exact IsGreenR.refl b
      | succ n ih => exact IsGreenR.trans hR_bz (IsGreenR.mul_left c ih)
    have hR_cib : IsGreenR b (g i) := hR_all i

    have h_b_eq_ckb : ∃ k > 0, b = L k b := by
      let k := j - i
      have hk_pos : 0 < k := Nat.sub_pos_of_lt hij
      have hk_eq_j : i + k = j := Nat.add_sub_of_le (le_of_lt hij)
      have h_shift : ∀ m, g (i + m) = L m (g i) := by
        intro m
        induction m with
        | zero => rfl
        | succ m ih =>
          calc g (i + (m + 1)) = g (i + m + 1) := rfl
            _ = c * g (i + m) := rfl
            _ = c * L m (g i) := by rw [ih]
            _ = L (m + 1) (g i) := rfl
      have h_gi_k : L k (g i) = g i := by
        calc L k (g i) = g (i + k) := (h_shift k).symm
          _ = g j := by rw [hk_eq_j]
          _ = g i := heq.symm
      use k, hk_pos
      rcases hR_cib.left with heq_b | ⟨v_outer, hv⟩
      · calc b = g i := heq_b
          _ = L k (g i) := h_gi_k.symm
          _ = L k b := by rw [heq_b]
      · calc b = g i * v_outer := hv
          _ = L k (g i) * v_outer := by rw [h_gi_k]
          _ = L k (g i * v_outer) := (h_mul_pull k (g i) v_outer).symm
          _ = L k b := by rw [← hv]

    rcases h_b_eq_ckb with ⟨k, hk_pos, hk_eq⟩

    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hk_pos)

    have h_pull_c : ∀ n x, L (n + 1) x = L n (c * x) := by
      intro n x
      induction n with
      | zero => rfl
      | succ n ih =>
        calc L (n + 1 + 1) x = c * L (n + 1) x := rfl
          _ = c * L n (c * x) := by rw [ih]
          _ = L (n + 1) (c * x) := rfl

    rcases hc_dvd with hc_eq_a | ⟨w, hw⟩
    · rcases m with _ | m_pred
      · have h_final : b = a * b := by
          calc b = L (0 + 1) b := hk_eq
            _ = L 0 (c * b) := h_pull_c 0 b
            _ = L 0 (a * b) := congrArg (fun x => L 0 (x * b)) hc_eq_a
            _ = a * b := rfl
        exact Or.inl h_final
      · have h_final : b = L m_pred c * (a * b) := by
          calc b = L (m_pred + 1 + 1) b := hk_eq
            _ = L (m_pred + 1) (c * b) := h_pull_c (m_pred + 1) b
            _ = L (m_pred + 1) (a * b) := congrArg (fun x => L (m_pred + 1) (x * b)) hc_eq_a
            _ = L m_pred (c * (a * b)) := h_pull_c m_pred (a * b)
            _ = L m_pred c * (a * b) := h_mul_pull m_pred c (a * b)
        exact Or.inr ⟨L m_pred c, h_final⟩
    · have h_final : b = L m w * (a * b) := by
        calc b = L (m + 1) b := hk_eq
          _ = L m (c * b) := h_pull_c m b
          _ = L m ((w * a) * b) := congrArg (fun x => L m (x * b)) hw
          _ = L m (w * (a * b)) := congrArg (L m) (mul_assoc w a b)
          _ = L m w * (a * b) := h_mul_pull m w (a * b)
      exact Or.inr ⟨L m w, h_final⟩

  exact ⟨h_b_dvd_ab, h_ab_dvd_b⟩

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
        calc a * a = a * b := congrArg (fun x => a * x) hab_eq
             _     = a     := h_a_eq.symm
      refine ⟨ha, idem, IsGreenL.refl a, ?_⟩
      rw [hab_eq]
    · use b
      have h1 : v * a = b := by
        calc v * a = v * (a * b) := congrArg (fun x => v * x) h_a_eq
             _     = b           := hv.symm
      have idem : b * b = b := by
        calc b * b = (v * a) * b := congrArg (fun x => x * b) h1.symm
             _     = v * (a * b) := mul_assoc v a b
             _     = b           := hv.symm
      have hLab : IsGreenL a b := ⟨Or.inr ⟨a, h_a_eq⟩, Or.inr ⟨v, h1.symm⟩⟩
      exact ⟨hb, idem, hLab, IsGreenR.refl b⟩
  · rcases h_b_dvd with h_b_eq | ⟨v, hv⟩
    · use a
      have h2 : b * u = a := by
        calc b * u = (a * b) * u := congrArg (fun x => x * u) h_b_eq
             _     = a           := hu.symm
      have idem : a * a = a := by
        calc a * a = a * (b * u) := congrArg (fun x => a * x) h2.symm
             _     = (a * b) * u := (mul_assoc a b u).symm
             _     = a           := hu.symm
      have hRba : IsGreenR b a := ⟨Or.inr ⟨b, h_b_eq⟩, Or.inr ⟨u, h2.symm⟩⟩
      exact ⟨ha, idem, IsGreenL.refl a, hRba⟩
    · use v * a
      have he_eq : v * a = b * u := by
        calc v * a = v * (a * b * u)   := congrArg (fun x => v * x) hu
             _     = (v * (a * b)) * u := (mul_assoc v (a * b) u).symm
             _     = b * u             := congrArg (fun x => x * u) hv.symm
      have idem : (v * a) * (v * a) = v * a := by
        calc (v * a) * (v * a) = (v * a) * (b * u) := congrArg (fun x => (v * a) * x) he_eq
             _ = v * (a * (b * u))                 := mul_assoc v a (b * u)
             _ = v * (a * b * u)                   :=
              congrArg (fun x => v * x) (mul_assoc a b u).symm
             _ = v * a                             := congrArg (fun x => v * x) hu.symm
      have hLae1 : a = a * (v * a) := by
        calc a = a * b * u   := hu
             _ = a * (b * u) := mul_assoc a b u
             _ = a * (v * a) := congrArg (fun x => a * x) he_eq.symm
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


-- Fact 2.6
theorem is_group_isGreenH_eqvClass_iff_idempotent
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


end GreensFacts
