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

-- Fact 2.2
theorem green_d_eq_j_of_finite [Fintype S] : (GreenD : S → S → Prop) = GreenJ := by
  sorry

-- Fact 2.3
theorem is_regular_d_class_iff_exists_idempotent [Fintype S] (D : Set S) (hD : ∃ x, D = greenDClass x) :
    IsRegularDClass D ↔ ∃ e ∈ D, e * e = e := by
  sorry

-- Fact 2.4
theorem mul_mem_green_d_properties [Fintype S] {D : Set S} (hD : ∃ x, D = greenDClass x)
    (a b : S) (ha : a ∈ D) (hb : b ∈ D) (hab : a * b ∈ D) :
    (GreenR a (a * b) ∧ GreenL b (a * b)) ∧
    (∃ e ∈ D, e * e = e ∧ GreenL a e ∧ GreenR b e) := by
  sorry

-- Fact 2.5
theorem card_green_h_eq_of_green_d [Fintype S] (a b : S) (h : GreenD a b) :
    Fintype.card (greenHClass a) = Fintype.card (greenHClass b) := by
  sorry

-- Fact 2.6
theorem is_group_green_h_iff_idempotent [Fintype S] (H : Set S) (hH : ∃ a, H = greenHClass a) :
    (∀ x y, x ∈ H → y ∈ H → x * y ∉ H) ∨
    (∃ e ∈ H, e * e = e ∧ ∀ x y, x ∈ H → y ∈ H → x * y ∈ H) := by
  sorry

end GreensFacts


section nD

variable [Fintype S]

noncomputable def nD (D : Set S) : ℕ :=
  if IsRegularDClass D then
    (Finset.univ.filter (fun x =>
      x ∈ D ∧ ∃ e ∈ D, e * e = e ∧ GreenH x e
    )).card
  else
    1

theorem nD_pos (D : Set S) (hD : ∃ x, D = greenDClass x) : 0 < nD D := by
  dsimp [nD]
  split_ifs with hReg
  · apply Finset.card_pos.mpr
    obtain ⟨e, heD, he_idem⟩ := (is_regular_d_class_iff_exists_idempotent D hD).mp hReg
    use e
    simp only [Finset.mem_univ, Finset.mem_filter, true_and]
    refine ⟨heD, e, heD, he_idem, ?_⟩
    exact green_h_refl e
  · exact Nat.zero_lt_one

instance (D : Set S) (hD : ∃ x, D = greenDClass x) : Nonempty (Fin (nD D)) :=
  Fin.pos_iff_nonempty.mp (nD_pos D hD)

end nD
