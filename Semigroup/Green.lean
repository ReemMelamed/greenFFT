import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Fintype.Card

/-!
# Green's Relations
-/

open Classical

variable {S : Type*} [Semigroup S]



section GreenDefinitions

def GreenLeftDvd (a b : S) : Prop := a = b ∨ ∃ z, a = z * b
def GreenRightDvd (a b : S) : Prop := a = b ∨ ∃ z, a = b * z

def GreenJRel (a b : S) : Prop :=
  a = b ∨ (∃ u, a = u * b) ∨ (∃ v, a = b * v) ∨ (∃ u v, a = u * b * v)

def GreenL (a b : S) : Prop := GreenLeftDvd a b ∧ GreenLeftDvd b a
def GreenR (a b : S) : Prop := GreenRightDvd a b ∧ GreenRightDvd b a
def GreenH (a b : S) : Prop := GreenL a b ∧ GreenR a b
def GreenD (a b : S) : Prop := ∃ z, GreenL a z ∧ GreenR z b
def GreenJ (a b : S) : Prop := GreenJRel a b ∧ GreenJRel b a

end GreenDefinitions



section GreenEquivalences

@[refl] theorem green_left_dvd_refl (a : S) : GreenLeftDvd a a := Or.inl rfl
@[refl] theorem green_right_dvd_refl (a : S) : GreenRightDvd a a := Or.inl rfl

@[trans] theorem green_left_dvd_trans {a b c : S} (hab : GreenLeftDvd a b) (hbc : GreenLeftDvd b c) : GreenLeftDvd a c := by
  rcases hab with rfl | ⟨x, hx⟩
  · exact hbc
  · rcases hbc with rfl | ⟨y, hy⟩
    · exact Or.inr ⟨x, hx⟩
    · exact Or.inr ⟨x * y, by rw [hx, hy, mul_assoc]⟩

@[trans] theorem green_right_dvd_trans {a b c : S} (hab : GreenRightDvd a b) (hbc : GreenRightDvd b c) : GreenRightDvd a c := by
  rcases hab with rfl | ⟨x, hx⟩
  · exact hbc
  · rcases hbc with rfl | ⟨y, hy⟩
    · exact Or.inr ⟨x, hx⟩
    · exact Or.inr ⟨y * x, by rw [hx, hy, mul_assoc]⟩

@[refl] theorem green_l_refl (a : S) : GreenL a a := ⟨green_left_dvd_refl a, green_left_dvd_refl a⟩
@[symm] theorem green_l_symm {a b : S} (h : GreenL a b) : GreenL b a := ⟨h.right, h.left⟩
@[trans] theorem green_l_trans {a b c : S} (hab : GreenL a b) (hbc : GreenL b c) : GreenL a c :=
  ⟨green_left_dvd_trans hab.left hbc.left, green_left_dvd_trans hbc.right hab.right⟩

theorem green_l_equivalence : Equivalence (GreenL : S → S → Prop) :=
  ⟨green_l_refl, green_l_symm, green_l_trans⟩

instance greenLSetoid : Setoid S := ⟨GreenL, green_l_equivalence⟩

@[refl] theorem green_r_refl (a : S) : GreenR a a := ⟨green_right_dvd_refl a, green_right_dvd_refl a⟩
@[symm] theorem green_r_symm {a b : S} (h : GreenR a b) : GreenR b a := ⟨h.right, h.left⟩
@[trans] theorem green_r_trans {a b c : S} (hab : GreenR a b) (hbc : GreenR b c) : GreenR a c :=
  ⟨green_right_dvd_trans hab.left hbc.left, green_right_dvd_trans hbc.right hab.right⟩

theorem green_r_equivalence : Equivalence (GreenR : S → S → Prop) :=
  ⟨green_r_refl, green_r_symm, green_r_trans⟩

instance greenRSetoid : Setoid S := ⟨GreenR, green_r_equivalence⟩

@[refl] theorem green_h_refl (a : S) : GreenH a a := ⟨green_l_refl a, green_r_refl a⟩

theorem green_h_equivalence : Equivalence (GreenH : S → S → Prop) := {
  refl := green_h_refl
  symm := fun h => ⟨green_l_symm h.left, green_r_symm h.right⟩
  trans := fun h1 h2 => ⟨green_l_trans h1.left h2.left, green_r_trans h1.right h2.right⟩
}

instance greenHSetoid : Setoid S := ⟨GreenH, green_h_equivalence⟩

lemma green_l_commutes_r {a b z : S} (hL : GreenL a z) (hR : GreenR z b) : ∃ z', GreenR a z' ∧ GreenL z' b := by
  have h_az : GreenLeftDvd a z := hL.left
  have h_za : GreenLeftDvd z a := hL.right
  have h_zb : GreenRightDvd z b := hR.left
  have h_bz : GreenRightDvd b z := hR.right
  rcases h_az with rfl | ⟨u, hu⟩; · exact ⟨b, hR, green_l_refl b⟩
  rcases h_za with rfl | ⟨v, hv⟩; · exact ⟨b, hR, green_l_refl b⟩
  rcases h_zb with rfl | ⟨x, hx⟩; · exact ⟨a, green_r_refl a, hL⟩
  rcases h_bz with rfl | ⟨y, hy⟩; · exact ⟨a, green_r_refl a, hL⟩
  use a * y
  have hR1 : GreenRightDvd a (a * y) := by
    right; use x; rw [hu, mul_assoc u z y, ← hy, mul_assoc u b x, ← hx]
  have hR2 : GreenRightDvd (a * y) a := by
    right; exact ⟨y, rfl⟩
  have hL1 : GreenLeftDvd (a * y) b := by
    right; use u; rw [hu, mul_assoc, ← hy]
  have hL2 : GreenLeftDvd b (a * y) := by
    right; use v; rw [← mul_assoc, ← hv, hy]
  exact ⟨⟨hR1, hR2⟩, ⟨hL1, hL2⟩⟩

theorem green_d_equivalence : Equivalence (GreenD : S → S → Prop) := {
  refl := fun x => ⟨x, green_l_refl x, green_r_refl x⟩
  symm := fun {x y} ⟨z, hL, hR⟩ => by
    obtain ⟨z', h_x_R_z', h_z'_L_y⟩ := green_l_commutes_r hL hR
    exact ⟨z', green_l_symm h_z'_L_y, green_r_symm h_x_R_z'⟩
  trans := fun {x y z} ⟨z1, h_x_L_z1, h_z1_R_y⟩ ⟨z2, h_y_L_z2, h_z2_R_z⟩ => by
    have h_z2_L_y : GreenL z2 y := green_l_symm h_y_L_z2
    have h_y_R_z1 : GreenR y z1 := green_r_symm h_z1_R_y
    obtain ⟨z3, h_z2_R_z3, h_z3_L_z1⟩ := green_l_commutes_r h_z2_L_y h_y_R_z1
    have h_z1_L_z3 : GreenL z1 z3 := green_l_symm h_z3_L_z1
    have h_z3_R_z2 : GreenR z3 z2 := green_r_symm h_z2_R_z3
    have h_x_L_z3 : GreenL x z3 := green_l_trans h_x_L_z1 h_z1_L_z3
    have h_z3_R_z : GreenR z3 z := green_r_trans h_z3_R_z2 h_z2_R_z
    exact ⟨z3, h_x_L_z3, h_z3_R_z⟩
}

instance greenDSetoid : Setoid S := ⟨GreenD, green_d_equivalence⟩

end GreenEquivalences



section GreenClasses

def greenLClass (x : S) : Set S := { y | GreenL y x }
def greenRClass (x : S) : Set S := { y | GreenR y x }
def greenHClass (x : S) : Set S := { y | GreenH y x }
def greenDClass (x : S) : Set S := { y | GreenD y x }

def IsGreenRegular (a : S) : Prop := ∃ s, a * s * a = a
def IsRegularDClass (D : Set S) : Prop := ∀ x ∈ D, IsGreenRegular x

end GreenClasses



section GreensFacts

-- Fact 2.1
theorem green_l_mul_right_and_r_mul_left (a b c : S) :
    (GreenL a b → GreenL (a * c) (b * c)) ∧
    (GreenR a b → GreenR (c * a) (c * b)) := by
  constructor
  · intro h
    have h1 : GreenLeftDvd a b := h.left
    have h2 : GreenLeftDvd b a := h.right
    constructor
    · rcases h1 with h_eq | ⟨z, hz⟩
      · left; rw [h_eq]
      · right; use z; rw [hz, mul_assoc]
    · rcases h2 with h_eq | ⟨z, hz⟩
      · left; rw [h_eq]
      · right; use z; rw [hz, mul_assoc]
  · intro h
    have h1 : GreenRightDvd a b := h.left
    have h2 : GreenRightDvd b a := h.right
    constructor
    · rcases h1 with h_eq | ⟨z, hz⟩
      · left; rw [h_eq]
      · right; use z; rw [hz, ← mul_assoc]
    · rcases h2 with h_eq | ⟨z, hz⟩
      · left; rw [h_eq]
      · right; use z; rw [hz, ← mul_assoc]


lemma green_d_implies_j_rel {a b : S} (h : GreenD a b) : GreenJRel a b := by
  rcases h with ⟨z, hL, hR⟩
  rcases hL.left with rfl | ⟨u, hu⟩
  · rcases hR.left with rfl | ⟨v, hv⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inl ⟨v, hv⟩))
  · rcases hR.left with rfl | ⟨v, hv⟩
    · exact Or.inr (Or.inl ⟨u, hu⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨u, v, by rw [hu, hv, mul_assoc]⟩))

lemma green_d_implies_j {a b : S} (h : GreenD a b) : GreenJ a b := by
  constructor
  · exact green_d_implies_j_rel h
  · have h_symm : GreenD b a := green_d_equivalence.symm h
    exact green_d_implies_j_rel h_symm

lemma green_j_implies_d [Fintype S] {a b : S} (h : GreenJ a b) : GreenD a b := by
  sorry

-- Fact 2.2
theorem green_d_eq_j_of_finite [Fintype S] : (GreenD : S → S → Prop) = GreenJ := by
  funext a b
  apply propext
  constructor
  · exact green_d_implies_j
  · exact green_j_implies_d


-- Fact 2.3
theorem is_regular_d_class_iff_exists_idempotent [Fintype S] (D : Set S) (hD : ∃ x, D = greenDClass x) :
    IsRegularDClass D ↔ ∃ e ∈ D, e * e = e := by
  obtain ⟨x₀, rfl⟩ := hD
  constructor
  · intro hReg
    have hx₀_in : x₀ ∈ greenDClass x₀ := green_d_equivalence.refl x₀
    obtain ⟨s, hs⟩ := hReg x₀ hx₀_in
    let e := x₀ * s
    have he_idem : e * e = e := by
      dsimp [e]
      rw [← mul_assoc (x₀ * s) x₀ s, hs]
    have he_R_x₀ : GreenR e x₀ := by
      constructor
      · right; exact ⟨s, rfl⟩
      · right; exact ⟨x₀, hs.symm⟩
    have he_D_x₀ : GreenD e x₀ := ⟨e, green_l_refl e, he_R_x₀⟩
    exact ⟨e, he_D_x₀, he_idem⟩
  · rintro ⟨e, heD, he_idem⟩
    intro y hyD
    have h_ye : GreenD y e := green_d_equivalence.trans hyD (green_d_equivalence.symm heD)
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


theorem green_l_cancellation {a x u v : S} (hx : GreenL x a) (h_cancel : a * u * v = a) :
    x * u * v = x := by
  rcases hx.left with rfl | ⟨k, rfl⟩
  · exact h_cancel
  · simp only [mul_assoc, h_cancel]

theorem green_r_cancellation {a x u v : S} (hx : GreenR x a) (h_cancel : v * u * a = a) :
    v * u * x = x := by
  rcases hx.left with rfl | ⟨k, rfl⟩
  · exact h_cancel
  · simp only [← mul_assoc, h_cancel]

noncomputable def equivHClassOfGreenR {a b : S} (h : GreenR a b) :
    greenHClass a ≃ greenHClass b := by
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
    · have hL1 : GreenL (x * z) (a * z) := (green_l_mul_right_and_r_mul_left x a z).1 hx.left
      have hL : GreenL (x * z) b := by rwa [← hz] at hL1
      have h_cancel_x : x * z * w = x := green_l_cancellation hx.left h_cancel_a
      have hdvd1 : GreenRightDvd (x * z) x := Or.inr ⟨z, rfl⟩
      have hdvd2 : GreenRightDvd x (x * z) := Or.inr ⟨w, h_cancel_x.symm⟩
      have hR1 : GreenR (x * z) x := ⟨hdvd1, hdvd2⟩
      have hR : GreenR (x * z) b := green_r_trans hR1 (green_r_trans hx.right h)
      exact ⟨hL, hR⟩
    · have hL1 : GreenL (y * w) (b * w) := (green_l_mul_right_and_r_mul_left y b w).1 hy.left
      have hL : GreenL (y * w) a := by rwa [← hw] at hL1
      have h_cancel_y : y * w * z = y := green_l_cancellation hy.left h_cancel_b
      have hdvd1 : GreenRightDvd (y * w) y := Or.inr ⟨w, rfl⟩
      have hdvd2 : GreenRightDvd y (y * w) := Or.inr ⟨z, h_cancel_y.symm⟩
      have hR1 : GreenR (y * w) y := ⟨hdvd1, hdvd2⟩
      have hR : GreenR (y * w) a := green_r_trans hR1 (green_r_trans hy.right (green_r_symm h))
      exact ⟨hL, hR⟩

noncomputable def equivHClassOfGreenL {a b : S} (h : GreenL a b) :
    greenHClass a ≃ greenHClass b := by
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
    · have hR1 : GreenR (z * x) (z * a) := (green_l_mul_right_and_r_mul_left x a z).2 hx.right
      have hR : GreenR (z * x) b := by rwa [← hz] at hR1
      have h_cancel_x : w * z * x = x := green_r_cancellation hx.right h_cancel_a
      have hdvd1 : GreenLeftDvd (z * x) x := Or.inr ⟨z, rfl⟩
      have hdvd2 : GreenLeftDvd x (z * x) := Or.inr ⟨w, by rw [← mul_assoc, h_cancel_x]⟩
      have hL1 : GreenL (z * x) x := ⟨hdvd1, hdvd2⟩
      have hL : GreenL (z * x) b := green_l_trans hL1 (green_l_trans hx.left h)
      exact ⟨hL, hR⟩
    · have hR1 : GreenR (w * y) (w * b) := (green_l_mul_right_and_r_mul_left y b w).2 hy.right
      have hR : GreenR (w * y) a := by rwa [← hw] at hR1
      have h_cancel_y : z * w * y = y := green_r_cancellation hy.right h_cancel_b
      have hdvd1 : GreenLeftDvd (w * y) y := Or.inr ⟨w, rfl⟩
      have hdvd2 : GreenLeftDvd y (w * y) := Or.inr ⟨z, by rw [← mul_assoc, h_cancel_y]⟩
      have hL1 : GreenL (w * y) y := ⟨hdvd1, hdvd2⟩
      have hL : GreenL (w * y) a := green_l_trans hL1 (green_l_trans hy.left (green_l_symm h))
      exact ⟨hL, hR⟩

-- Fact 2.5
theorem card_green_h_eq_of_green_d [Fintype S] (a b : S) (h : GreenD a b) :
    Fintype.card (greenHClass a) = Fintype.card (greenHClass b) := by
  rcases h with ⟨z, hL, hR⟩
  let equiv_az := equivHClassOfGreenL hL
  let equiv_zb := equivHClassOfGreenR hR
  trans Fintype.card (greenHClass z)
  · exact Fintype.card_congr equiv_az
  · exact Fintype.card_congr equiv_zb


-- Fact 2.4
theorem mul_mem_green_d_properties [Fintype S] {D : Set S} (hD : ∃ x, D = greenDClass x)
    (a b : S) (ha : a ∈ D) (hb : b ∈ D) (hab : a * b ∈ D) :
    (GreenR a (a * b) ∧ GreenL b (a * b)) ∧
    (∃ e ∈ D, e * e = e ∧ GreenL a e ∧ GreenR b e) := by
  sorry


-- Fact 2.6
theorem is_group_green_h_iff_idempotent [Fintype S] (H : Set S) (hH : ∃ a, H = greenHClass a) :
  (∀ x y, x ∈ H → y ∈ H → x * y ∉ H) ∨
  (∃ e ∈ H, e * e = e ∧ ∀ x y, x ∈ H → y ∈ H → x * y ∈ H) := by
  obtain ⟨a, rfl⟩ := hH
  by_cases h : ∀ x y, x ∈ greenHClass a → y ∈ greenHClass a → x * y ∉ greenHClass a
  · exact Or.inl h
  · right
    push_neg at h
    obtain ⟨x₀, y₀, hx₀, hy₀, hxy₀⟩ := h
    have hx₀H : GreenH x₀ a := hx₀
    have hy₀H : GreenH y₀ a := hy₀
    have hxy₀H : GreenH (x₀ * y₀) a := hxy₀
    have hx₀D : x₀ ∈ greenDClass a := by
      simp only [greenDClass, Set.mem_setOf_eq]
      exact ⟨a, hx₀H.left, green_r_refl a⟩
    have hy₀D : y₀ ∈ greenDClass a := by
      simp only [greenDClass, Set.mem_setOf_eq]
      exact ⟨a, hy₀H.left, green_r_refl a⟩
    have hxy₀D : x₀ * y₀ ∈ greenDClass a := by
      simp only [greenDClass, Set.mem_setOf_eq]
      exact ⟨a, hxy₀H.left, green_r_refl a⟩
    obtain ⟨_, e, heD, he_idem, hLx₀e, hRy₀e⟩ :=
      mul_mem_green_d_properties (D := greenDClass a) ⟨a, rfl⟩ x₀ y₀ hx₀D hy₀D hxy₀D
    have hLx₀a : GreenL x₀ a := hx₀H.left
    have hRy₀a : GreenR y₀ a := hy₀H.right
    have hLae : GreenL a e := green_l_trans (green_l_symm hLx₀a) hLx₀e
    have hRae : GreenR a e := green_r_trans (green_r_symm hRy₀a) hRy₀e
    have heH : e ∈ greenHClass a := ⟨green_l_symm hLae, green_r_symm hRae⟩
    refine ⟨e, heH, he_idem, ?_⟩
    intro u v huH hvH
    have hue : GreenH u e := green_h_equivalence.trans huH (green_h_equivalence.symm heH)
    have hve : GreenH v e := green_h_equivalence.trans hvH (green_h_equivalence.symm heH)
    have hLue : GreenL u e := hue.left
    have hRve : GreenR v e := hve.right
    have hev : e * v = v := by
      rcases hRve.left with rfl | ⟨z, hz⟩
      · exact he_idem
      · rw [hz, ← mul_assoc, he_idem]
    have hue_eq : u * e = u := by
      rcases hLue.left with rfl | ⟨w, hw⟩
      · exact he_idem
      · rw [hw, mul_assoc, he_idem]
    have hLuv_ev : GreenL (u * v) (e * v) := (green_l_mul_right_and_r_mul_left u e v).1 hLue
    have hLuv_v : GreenL (u * v) v := by rwa [hev] at hLuv_ev
    have hRuv_ue : GreenR (u * v) (u * e) := (green_l_mul_right_and_r_mul_left v e u).2 hRve
    have hRuv_u : GreenR (u * v) u := by rwa [hue_eq] at hRuv_ue
    have hLuv_a : GreenL (u * v) a := green_l_trans hLuv_v hvH.left
    have hRuv_a : GreenR (u * v) a := green_r_trans hRuv_u huH.right
    exact ⟨hLuv_a, hRuv_a⟩

end GreensFacts
