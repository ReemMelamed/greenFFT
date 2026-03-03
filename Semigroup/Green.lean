import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Fintype.Card

/-!
# Green's Relations
-/

variable {S : Type*} [Semigroup S]



section GreenDefinitions

def IsGreenLeftDvd (a b : S) : Prop := a = b ∨ ∃ z, a = z * b
def IsGreenRightDvd (a b : S) : Prop := a = b ∨ ∃ z, a = b * z

def IsGreenJRel (a b : S) : Prop :=
  a = b ∨ (∃ u, a = u * b) ∨ (∃ v, a = b * v) ∨ (∃ u v, a = u * b * v)

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

@[refl] theorem refl (a : S) : IsGreenJRel a a := Or.inl rfl

@[trans] theorem trans {a b c : S} (hab : IsGreenJRel a b)
  (hbc : IsGreenJRel b c) : IsGreenJRel a c := by
  rcases hab with rfl | ⟨x1, rfl⟩ | ⟨y1, rfl⟩ | ⟨x1, y1, rfl⟩
  · exact hbc

  · rcases hbc with rfl | ⟨x2, rfl⟩ | ⟨y2, rfl⟩ | ⟨x2, y2, rfl⟩
    · exact Or.inr (Or.inl ⟨x1, rfl⟩)
    · exact Or.inr (Or.inl ⟨x1 * x2, by simp [mul_assoc]⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨x1, y2, by simp [mul_assoc]⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨x1 * x2, y2, by simp [mul_assoc]⟩))

  · rcases hbc with rfl | ⟨x2, rfl⟩ | ⟨y2, rfl⟩ | ⟨x2, y2, rfl⟩
    · exact Or.inr (Or.inr (Or.inl ⟨y1, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨x2, y1, by simp [mul_assoc]⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨y2 * y1, by simp [mul_assoc]⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨x2, y2 * y1, by simp [mul_assoc]⟩))

  · rcases hbc with rfl | ⟨x2, rfl⟩ | ⟨y2, rfl⟩ | ⟨x2, y2, rfl⟩
    · exact Or.inr (Or.inr (Or.inr ⟨x1, y1, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨x1 * x2, y1, by simp [mul_assoc]⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨x1, y2 * y1, by simp [mul_assoc]⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨x1 * x2, y2 * y1, by simp [mul_assoc]⟩))
lemma of_mul_mul {a b u v : S} (h : a = u * b * v) : IsGreenJRel a b :=
  Or.inr (Or.inr (Or.inr ⟨u, v, h⟩))

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
def eqvClass (x : S) : Set S := { y | IsGreenL y x }
end IsGreenL

namespace IsGreenR
def eqvClass (x : S) : Set S := { y | IsGreenR y x }
end IsGreenR

namespace IsGreenH
def eqvClass (x : S) : Set S := { y | IsGreenH y x }
end IsGreenH

namespace IsGreenD
def eqvClass (x : S) : Set S := { y | IsGreenD y x }
end IsGreenD

namespace IsGreenJ
def eqvClass (x : S) : Set S := { y | IsGreenJ y x }
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

-- Fact 2.1
theorem green_l_mul_right_and_r_mul_left (a b c : S) :
    (IsGreenL a b → IsGreenL (a * c) (b * c)) ∧
    (IsGreenR a b → IsGreenR (c * a) (c * b)) := by
  constructor
  · intro h
    have h1 : IsGreenLeftDvd a b := h.left
    have h2 : IsGreenLeftDvd b a := h.right
    constructor
    · rcases h1 with h_eq | ⟨z, hz⟩
      · left; rw [h_eq]
      · right; use z; rw [hz, mul_assoc]
    · rcases h2 with h_eq | ⟨z, hz⟩
      · left; rw [h_eq]
      · right; use z; rw [hz, mul_assoc]
  · intro h
    have h1 : IsGreenRightDvd a b := h.left
    have h2 : IsGreenRightDvd b a := h.right
    constructor
    · rcases h1 with h_eq | ⟨z, hz⟩
      · left; rw [h_eq]
      · right; use z; rw [hz, ← mul_assoc]
    · rcases h2 with h_eq | ⟨z, hz⟩
      · left; rw [h_eq]
      · right; use z; rw [hz, ← mul_assoc]


lemma green_d_implies_j_rel {a b : S} (h : IsGreenD a b) : IsGreenJRel a b := by
  rcases h with ⟨z, hL, hR⟩
  rcases hL.left with rfl | ⟨u, hu⟩
  · rcases hR.left with rfl | ⟨v, hv⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inl ⟨v, hv⟩))
  · rcases hR.left with rfl | ⟨v, hv⟩
    · exact Or.inr (Or.inl ⟨u, hu⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨u, v, by rw [hu, hv, mul_assoc]⟩))

lemma green_d_implies_j {a b : S} (h : IsGreenD a b) : IsGreenJ a b := by
  constructor
  · exact green_d_implies_j_rel h
  · have h_symm : IsGreenD b a := IsGreenD.symm h
    exact green_d_implies_j_rel h_symm

lemma green_j_implies_d [Fintype S] {a b : S} (h : IsGreenJ a b) : IsGreenD a b := by
  sorry

-- Fact 2.2
theorem green_d_eq_j_of_finite [Fintype S] : (IsGreenD : S → S → Prop) = IsGreenJ := by
  funext a b
  apply propext
  constructor
  · exact green_d_implies_j
  · exact green_j_implies_d


-- Fact 2.3
theorem is_regular_d_class_iff_exists_idempotent [Fintype S] (D : Set S) (hD : ∃ x, D = IsGreenD.eqvClass x) :
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


theorem green_l_cancellation {a x u v : S} (hx : IsGreenL x a) (h_cancel : a * u * v = a) :
    x * u * v = x := by
  rcases hx.left with rfl | ⟨k, rfl⟩
  · exact h_cancel
  · simp only [mul_assoc, h_cancel]

theorem green_r_cancellation {a x u v : S} (hx : IsGreenR x a) (h_cancel : v * u * a = a) :
    v * u * x = x := by
  rcases hx.left with rfl | ⟨k, rfl⟩
  · exact h_cancel
  · simp only [← mul_assoc, h_cancel]

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
      left_inv := fun ⟨x, hx⟩ => Subtype.ext (by dsimp only; exact green_l_cancellation hx.left h_cancel_a)
      right_inv := fun ⟨y, hy⟩ => Subtype.ext (by dsimp only; exact green_l_cancellation hy.left h_cancel_b)
    }
    · have hL1 : IsGreenL (x * z) (a * z) := (green_l_mul_right_and_r_mul_left x a z).1 hx.left
      have hL : IsGreenL (x * z) b := by rwa [← hz] at hL1
      have h_cancel_x : x * z * w = x := green_l_cancellation hx.left h_cancel_a
      have hdvd1 : IsGreenRightDvd (x * z) x := Or.inr ⟨z, rfl⟩
      have hdvd2 : IsGreenRightDvd x (x * z) := Or.inr ⟨w, h_cancel_x.symm⟩
      have hR1 : IsGreenR (x * z) x := ⟨hdvd1, hdvd2⟩
      have hR : IsGreenR (x * z) b := IsGreenR.trans hR1 (IsGreenR.trans hx.right h)
      exact ⟨hL, hR⟩
    · have hL1 : IsGreenL (y * w) (b * w) := (green_l_mul_right_and_r_mul_left y b w).1 hy.left
      have hL : IsGreenL (y * w) a := by rwa [← hw] at hL1
      have h_cancel_y : y * w * z = y := green_l_cancellation hy.left h_cancel_b
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
      left_inv := fun ⟨x, hx⟩ => Subtype.ext (by dsimp only; rw [← mul_assoc]; exact green_r_cancellation hx.right h_cancel_a)
      right_inv := fun ⟨y, hy⟩ => Subtype.ext (by dsimp only; rw [← mul_assoc]; exact green_r_cancellation hy.right h_cancel_b)
    }
    · have hR1 : IsGreenR (z * x) (z * a) := (green_l_mul_right_and_r_mul_left x a z).2 hx.right
      have hR : IsGreenR (z * x) b := by rwa [← hz] at hR1
      have h_cancel_x : w * z * x = x := green_r_cancellation hx.right h_cancel_a
      have hdvd1 : IsGreenLeftDvd (z * x) x := Or.inr ⟨z, rfl⟩
      have hdvd2 : IsGreenLeftDvd x (z * x) := Or.inr ⟨w, by rw [← mul_assoc, h_cancel_x]⟩
      have hL1 : IsGreenL (z * x) x := ⟨hdvd1, hdvd2⟩
      have hL : IsGreenL (z * x) b := IsGreenL.trans hL1 (IsGreenL.trans hx.left h)
      exact ⟨hL, hR⟩
    · have hR1 : IsGreenR (w * y) (w * b) := (green_l_mul_right_and_r_mul_left y b w).2 hy.right
      have hR : IsGreenR (w * y) a := by rwa [← hw] at hR1
      have h_cancel_y : z * w * y = y := green_r_cancellation hy.right h_cancel_b
      have hdvd1 : IsGreenLeftDvd (w * y) y := Or.inr ⟨w, rfl⟩
      have hdvd2 : IsGreenLeftDvd y (w * y) := Or.inr ⟨z, by rw [← mul_assoc, h_cancel_y]⟩
      have hL1 : IsGreenL (w * y) y := ⟨hdvd1, hdvd2⟩
      have hL : IsGreenL (w * y) a := IsGreenL.trans hL1 (IsGreenL.trans hy.left (IsGreenL.symm h))
      exact ⟨hL, hR⟩

-- Fact 2.5
open Classical in
theorem card_green_h_eq_of_green_d [Fintype S] (a b : S) (h : IsGreenD a b) :
    Fintype.card (IsGreenH.eqvClass a) = Fintype.card (IsGreenH.eqvClass b) := by
  rcases h with ⟨z, hL, hR⟩
  let equiv_az := equivHClassOfIsGreenL hL
  let equiv_zb := equivHClassOfIsGreenR hR
  trans Fintype.card (IsGreenH.eqvClass z)
  · exact Fintype.card_congr equiv_az
  · exact Fintype.card_congr equiv_zb


-- Fact 2.4
theorem mul_mem_green_d_properties [Fintype S] {D : Set S} (hD : ∃ x, D = IsGreenD.eqvClass x)
    (a b : S) (ha : a ∈ D) (hb : b ∈ D) (hab : a * b ∈ D) :
    (IsGreenR a (a * b) ∧ IsGreenL b (a * b)) ∧
    (∃ e ∈ D, e * e = e ∧ IsGreenL a e ∧ IsGreenR b e) := by
  sorry


-- Fact 2.6
theorem is_group_green_h_iff_idempotent [Fintype S] (H : Set S) (hH : ∃ a, H = IsGreenH.eqvClass a) :
  (∀ x y, x ∈ H → y ∈ H → x * y ∉ H) ∨
  (∃ e ∈ H, e * e = e ∧ ∀ x y, x ∈ H → y ∈ H → x * y ∈ H) := by
  obtain ⟨a, rfl⟩ := hH
  by_cases h : ∀ x y, x ∈ IsGreenH.eqvClass a → y ∈ IsGreenH.eqvClass a → x * y ∉ IsGreenH.eqvClass a
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
      mul_mem_green_d_properties (D := IsGreenD.eqvClass a) ⟨a, rfl⟩ x₀ y₀ hx₀D hy₀D hxy₀D
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
    have hLuv_ev : IsGreenL (u * v) (e * v) := (green_l_mul_right_and_r_mul_left u e v).1 hLue
    have hLuv_v : IsGreenL (u * v) v := by rwa [hev] at hLuv_ev
    have hRuv_ue : IsGreenR (u * v) (u * e) := (green_l_mul_right_and_r_mul_left v e u).2 hRve
    have hRuv_u : IsGreenR (u * v) u := by rwa [hue_eq] at hRuv_ue
    have hLuv_a : IsGreenL (u * v) a := IsGreenL.trans hLuv_v hvH.left
    have hRuv_a : IsGreenR (u * v) a := IsGreenR.trans hRuv_u huH.right
    exact ⟨hLuv_a, hRuv_a⟩

end GreensFacts
