import Mathlib.Order.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

import Semigroup.Green

/-!
# The Factorisation Forest Theorem
-/

open Classical

section SplitDefinitions

variable {S α : Type*} [Semigroup S] [LinearOrder α]

variable {h : ℕ}

structure MultiplicativeLabeling (S α : Type*) [Semigroup S] [LinearOrder α] where
  σ: α → α → S
  prop : ∀ x y z : α, x < y → y < z → σ x y * σ y z = σ x z

abbrev Split (α : Type*) (h : ℕ) := α → Fin h

def SplitRelation (s : Split α h) (x y : α) : Prop :=
  s x = s y ∧ ∀ z, min x y ≤ z → z ≤ max x y → s z ≤ s (min x y)

def IsNormalized [Fintype α] [Nonempty α] [Nonempty (Fin h)] (s : Split α h) : Prop :=
  let min_α := Finset.min' Finset.univ Finset.univ_nonempty
  s min_α = Finset.max' Finset.univ Finset.univ_nonempty

def IsRamsey (L : MultiplicativeLabeling S α) (s : Split α h) : Prop :=
  ∀ x y : α, x<y → SplitRelation s x y → L.σ x y * L.σ x y = L.σ x y

theorem split_relation_equiv (s : Split α h) : Equivalence (SplitRelation s) := by
  constructor <;> grind [SplitRelation]

end SplitDefinitions


section GroupCase

variable {G α : Type*} [Group G] [Fintype G] [LinearOrder α] [Fintype α] [Nonempty α]

lemma simon_group_case (σ : MultiplicativeLabeling G α) :
    ∃ (s : Split α (Fintype.card G)), IsNormalized s ∧ IsRamsey σ s := by
  let size_G := Fintype.card G
  let x₀ : α := Finset.min' .univ Finset.univ_nonempty

  have h_size_cast : size_G - 1 + 1 = size_G := by grind [Fintype.card_pos]
  haveI : Nonempty (Fin size_G) := by grind [Fintype.card_pos, Fin.pos_iff_nonempty]

  let max_rank : Fin size_G := Fin.cast h_size_cast (Fin.last (size_G - 1))

  let raw_equiv := Fintype.equivFin G
  let index_in_enum := raw_equiv.trans (Equiv.swap (raw_equiv 1) max_rank)

  let s : Split α size_G := fun y =>
    if y = x₀ then max_rank else index_in_enum (σ.σ x₀ y)
  use s

  constructor
  · unfold IsNormalized
    simp [s, x₀]
    symm
    rw [Finset.max'_eq_iff]
    constructor
    · apply Finset.mem_univ
    · intro hy _
      apply Fin.le_iff_val_le_val.mpr
      simp only [max_rank, Fin.val_cast, Fin.val_last]
      exact Nat.le_pred_of_lt hy.is_lt

  · intros x y hlt hsr
    unfold SplitRelation at hsr

    by_cases hx : x = x₀
    · subst hx
      have h_eq : s x₀ = s y := hsr.left
      have h_sx0 : s x₀ = max_rank := by simp [s]
      have h_y_ne : y ≠ x₀ := ne_of_gt hlt
      have h_sy : s y = index_in_enum (σ.σ x₀ y) := by simp [s, h_y_ne]

      rw [h_sx0, h_sy] at h_eq
      have h_map_1 : index_in_enum 1 = max_rank := by
        simp [index_in_enum]

      rw [← h_map_1] at h_eq
      have h_val_1 : σ.σ x₀ y = 1 := Equiv.injective index_in_enum h_eq.symm
      simp [h_val_1]

    · have h_x0_lt_x : x₀ < x :=
        lt_of_le_of_ne (Finset.min'_le (.univ) x (Finset.mem_univ x)) (ne_comm.mp hx)

      have h_sx : s x = index_in_enum (σ.σ x₀ x) := by simp [s, ne_of_gt h_x0_lt_x]
      have h_x0_lt_y : x₀ < y := lt_trans h_x0_lt_x hlt
      have h_sy : s y = index_in_enum (σ.σ x₀ y) := by simp [s, ne_of_gt h_x0_lt_y]

      have h_s_eq : s x = s y := hsr.left
      rw [h_sx, h_sy] at h_s_eq

      have h_vals_eq : σ.σ x₀ x = σ.σ x₀ y := Equiv.injective index_in_enum h_s_eq
      have h_mult := σ.prop x₀ x y h_x0_lt_x hlt

      rw [← h_vals_eq] at h_mult
      have h_res : σ.σ x y = 1 := by
        have h_temp := congr_arg (fun g => (σ.σ x₀ x)⁻¹ * g) h_mult
        simp only [inv_mul_cancel_left, inv_mul_cancel] at h_temp
        exact h_temp

      simp [h_res]

end GroupCase


section HClassWrapper

variable {S α : Type*} [Semigroup S] [LinearOrder α]

lemma simon_hclass_case
    (σ : MultiplicativeLabeling S α)
    (X : Set α) [Nonempty X] [Fintype X]
    (H : Set S) [Group H] [Fintype H]
    (h_mul_eq : ∀ a b : H, (a * b : S) = (a * b : H))
    (h_range : ∀ x y : α, x ∈ X → y ∈ X → x < y → σ.σ x y ∈ H) :
    ∃ (s : Split X (Fintype.card H)),
      IsNormalized s ∧
      (∀ x y : X, (x : α) < (y : α) → SplitRelation s x y →
        σ.σ (x : α) (y : α) * σ.σ (x : α) (y : α) = σ.σ (x : α) (y : α)) := by
  let σ_H_fun : X → X → H := fun x y =>
    if h : (x : α) < (y : α) then
      ⟨σ.σ (x : α) (y : α), h_range (x : α) (y : α) x.property y.property h⟩
    else
      1

  have σ_H_prop : ∀ (x y z : X), x < y → y < z → σ_H_fun x y * σ_H_fun y z = σ_H_fun x z := by
      intro x y z hxy hyz
      have hxy_val : (x : α) < (y : α) := hxy
      have hyz_val : (y : α) < (z : α) := hyz
      have hxz_val : (x : α) < (z : α) := lt_trans hxy_val hyz_val
      ext
      rw [← h_mul_eq]
      simp only [σ_H_fun, dif_pos hxy_val, dif_pos hyz_val, dif_pos hxz_val, Subtype.coe_mk]
      exact σ.prop (x : α) (y : α) (z : α) hxy_val hyz_val

  let σ_H : MultiplicativeLabeling H X := ⟨σ_H_fun, σ_H_prop⟩

  obtain ⟨s_H, h_norm, h_ramsey⟩ := simon_group_case σ_H

  use s_H
  constructor
  · exact h_norm
  · intro x y hxy h_split
    have h_ramsey_xy := h_ramsey x y hxy h_split
    have h_val : σ_H.σ x y = ⟨σ.σ (x : α) (y : α), h_range (x : α) (y : α) x.property y.property hxy⟩ := by
      simp only [σ_H, σ_H_fun, hxy, dif_pos]
    have h_eq_in_S := congr_arg Subtype.val h_ramsey_xy
    simp only [h_val] at h_eq_in_S
    rw [← h_mul_eq] at h_eq_in_S
    exact h_eq_in_S

end HClassWrapper


section RegularDClassCase

variable {S α : Type*} [Semigroup S] [Fintype S] [LinearOrder α] [Fintype α] [Nonempty α]

lemma simon_regular_d_case
    (σ : MultiplicativeLabeling S α)
    (D : Set S)
    (hD : ∃ x, D = greenDClass x)
    (h_ne : Nonempty (Fin (nD D)) := Fin.pos_iff_nonempty.mp (nD_pos D hD))
    (hReg : IsRegularDClass D)
    (h_range : ∀ x y, x < y → σ.σ x y ∈ D) :
    ∃ (s : Split α (nD D)), IsNormalized s ∧ IsRamsey σ s := by

  obtain ⟨x₀, hx₀⟩ := hD

  have h_idem_L : ∀ a ∈ D, ∃ e ∈ greenLClass a, e * e = e := by
    intro a ha
    obtain ⟨s, hs⟩ := hReg a ha
    use s * a
    constructor
    · constructor
      · right; use s
      · right; use a; calc a = a * s * a := hs.symm
                           _ = a * (s * a) := by rw [mul_assoc]
    · calc (s * a) * (s * a) = s * (a * s * a) := by simp [mul_assoc]
      _ = s * a := by rw [hs]

  have h_idem_R : ∀ a ∈ D, ∃ e ∈ greenRClass a, e * e = e := by
    intro a ha
    obtain ⟨s, hs⟩ := hReg a ha
    use a * s
    constructor
    · constructor
      · right; use s
      · right; use a; calc a = a * s * a := hs.symm
                           _ = (a * s) * a := by rw [mul_assoc]
    · calc (a * s) * (a * s) = (a * s * a) * s := by simp [mul_assoc]
      _ = a * s := by rw [hs]

  let is_max (x : α) : Prop := ∀ y, y ≤ x
  let is_min (x : α) : Prop := ∀ y, x ≤ y

  let L_of (x : α) : Set S :=
    if h_min : is_min x then
      if h_max : is_max x then
        greenLClass x₀
      else
        have h_exists : ∃ y, x < y := by contrapose! h_max; exact h_max
        let y := Classical.choose h_exists
        have ha_D : σ.σ x y ∈ D := h_range x y (Classical.choose_spec h_exists)
        greenLClass (Classical.choose (h_idem_R (σ.σ x y) ha_D))
    else
      have h_exists : ∃ y, y < x := by contrapose! h_min; exact h_min
      let y := Classical.choose h_exists
      greenLClass (σ.σ y x)

  have h_L_well : ∀ x y1 y2 (h_not_min : ¬ is_min x) (hy1 : y1 < x) (hy2 : y2 < x),
      greenLClass (σ.σ y1 x) = greenLClass (σ.σ y2 x) := by
    intro x y1 y2 h_not_min hy1 hy2
    wlog h_le : y1 ≤ y2 generalizing y1 y2 hy1 hy2
    · exact (this y2 y1 hy2 hy1 (not_le.mp h_le).le).symm
    · rcases h_le.eq_or_lt with rfl | h_lt
      · rfl
      · have h_prod : σ.σ y1 x = σ.σ y1 y2 * σ.σ y2 x := (σ.prop y1 y2 x h_lt hy2).symm
        have h12 : σ.σ y1 y2 ∈ D := h_range y1 y2 h_lt
        have h2x : σ.σ y2 x ∈ D := h_range y2 x hy2
        have h1x : σ.σ y1 x ∈ D := h_range y1 x hy1
        have hL_raw := (mul_mem_green_d_properties ⟨x₀, hx₀⟩ (σ.σ y1 y2) (σ.σ y2 x) h12 h2x (h_prod ▸ h1x)).1.2
        have hL : GreenL (σ.σ y2 x) (σ.σ y1 x) := h_prod ▸ hL_raw
        ext z
        constructor
        · intro hz; exact green_l_trans hz (green_l_symm hL)
        · intro hz; exact green_l_trans hz hL

  let R_of (x : α) : Set S :=
    if h_max : is_max x then
      if h_min : is_min x then
        have ha_D : x₀ ∈ D := by
          rw [hx₀]
          exact green_d_equivalence.refl x₀
        greenRClass (Classical.choose (h_idem_L x₀ ha_D))
      else
        have h_exists : ∃ y, y < x := by contrapose! h_min; exact h_min
        let y := Classical.choose h_exists
        have ha_D : σ.σ y x ∈ D := h_range y x (Classical.choose_spec h_exists)
        greenRClass (Classical.choose (h_idem_L (σ.σ y x) ha_D))
    else
      have h_exists : ∃ y, x < y := by contrapose! h_max; exact h_max
      let y := Classical.choose h_exists
      greenRClass (σ.σ x y)

  have h_R_well : ∀ x y1 y2 (h_not_max : ¬ is_max x) (hy1 : x < y1) (hy2 : x < y2),
      greenRClass (σ.σ x y1) = greenRClass (σ.σ x y2) := by
    intro x y1 y2 h_not_max hy1 hy2
    wlog h_le : y1 ≤ y2 generalizing y1 y2 hy1 hy2
    · exact (this y2 y1 hy2 hy1 (not_le.mp h_le).le).symm
    · rcases h_le.eq_or_lt with rfl | h_lt
      · rfl
      · have h_prod : σ.σ x y1 * σ.σ y1 y2 = σ.σ x y2 := σ.prop x y1 y2 hy1 h_lt
        have hx1 : σ.σ x y1 ∈ D := h_range x y1 hy1
        have h12 : σ.σ y1 y2 ∈ D := h_range y1 y2 h_lt
        have hx2 : σ.σ x y2 ∈ D := h_range x y2 hy2
        have hR_raw := (mul_mem_green_d_properties ⟨x₀, hx₀⟩ (σ.σ x y1) (σ.σ y1 y2) hx1 h12 (h_prod.symm ▸ hx2)).1.1
        have hR : GreenR (σ.σ x y1) (σ.σ x y2) := h_prod ▸ hR_raw
        ext z
        constructor
        · intro hz; exact green_r_trans hz hR
        · intro hz; exact green_r_trans hz (green_r_symm hR)

  let H_of (x : α) : Set S := L_of x ∩ R_of x

  have h_H_idem : ∀ x, ∃ e ∈ H_of x, e * e = e := by
    intro x
    dsimp [H_of]
    by_cases h_min : is_min x
    · by_cases h_max : is_max x
      · have ha_D : x₀ ∈ D := by
          rw [hx₀]
          exact green_d_equivalence.refl x₀
        let e := Classical.choose (h_idem_L x₀ ha_D)
        have he_prop := Classical.choose_spec (h_idem_L x₀ ha_D)
        use e
        refine ⟨⟨?_, ?_⟩, he_prop.right⟩
        · simp only [L_of, h_min, h_max, dite_true]
          exact he_prop.left
        · simp only [R_of, h_max, h_min, dite_true]
          exact green_r_refl e
      · have h_exists : ∃ y, x < y := by contrapose! h_max; exact h_max
        have ha_D : σ.σ x (Classical.choose h_exists) ∈ D := h_range x _ (Classical.choose_spec h_exists)
        let e := Classical.choose (h_idem_R (σ.σ x (Classical.choose h_exists)) ha_D)
        have he_prop := Classical.choose_spec (h_idem_R (σ.σ x (Classical.choose h_exists)) ha_D)
        use e
        refine ⟨⟨?_, ?_⟩, he_prop.right⟩
        · simp only [L_of, h_min, h_max, dite_true, dite_false]
          exact green_l_refl e
        · simp only [R_of, h_max, dite_false]
          exact he_prop.left
    · by_cases h_max : is_max x
      · have h_exists : ∃ y, y < x := by contrapose! h_min; exact h_min
        have ha_D : σ.σ (Classical.choose h_exists) x ∈ D := h_range _ x (Classical.choose_spec h_exists)
        let e := Classical.choose (h_idem_L (σ.σ (Classical.choose h_exists) x) ha_D)
        have he_prop := Classical.choose_spec (h_idem_L (σ.σ (Classical.choose h_exists) x) ha_D)
        use e
        refine ⟨⟨?_, ?_⟩, he_prop.right⟩
        · simp only [L_of, h_min, dite_false]
          exact he_prop.left
        · simp only [R_of, h_max, h_min, dite_true, dite_false]
          exact green_r_refl e
      · have hy : ∃ y, y < x := by contrapose! h_min; exact h_min
        have hz : ∃ z, x < z := by contrapose! h_max; exact h_max
        have ha : σ.σ (Classical.choose hy) x ∈ D := h_range _ _ (Classical.choose_spec hy)
        have hb : σ.σ x (Classical.choose hz) ∈ D := h_range _ _ (Classical.choose_spec hz)
        have hab : σ.σ (Classical.choose hy) x * σ.σ x (Classical.choose hz) ∈ D := by
          rw [σ.prop _ _ _ (Classical.choose_spec hy) (Classical.choose_spec hz)]
          exact h_range _ _ (lt_trans (Classical.choose_spec hy) (Classical.choose_spec hz))
        obtain ⟨_, ⟨e, _, he_idem, hLe, hRe⟩⟩ :=
          mul_mem_green_d_properties ⟨x₀, hx₀⟩ (σ.σ (Classical.choose hy) x) (σ.σ x (Classical.choose hz)) ha hb hab
        use e
        refine ⟨⟨?_, ?_⟩, he_idem⟩
        · simp only [L_of, h_min, dite_false]
          exact green_l_symm hLe
        · simp only [R_of, h_max, dite_false]
          exact green_r_symm hRe

  let G_D := { y : S // y ∈ D ∧ ∃ e ∈ D, e * e = e ∧ GreenH y e }

  have h_card_G_D : Fintype.card G_D = nD D := by
    dsimp [nD]
    rw [if_pos hReg]
    exact Fintype.card_subtype (fun y => y ∈ D ∧ ∃ e ∈ D, e * e = e ∧ GreenH y e)

  have h_card_pos : 0 < Fintype.card G_D := by
    rw [h_card_G_D]
    exact Fin.pos_iff_nonempty.mpr h_ne

  haveI h_nonempty_GD : Nonempty G_D := Fintype.card_pos_iff.mp h_card_pos

  have h_size_cast : Fintype.card G_D - 1 + 1 = Fintype.card G_D :=
    Nat.sub_add_cancel h_card_pos

  let max_rank : Fin (nD D) := 
    Fin.cast h_card_G_D (Fin.cast h_size_cast (Fin.last (Fintype.card G_D - 1)))

  let equiv_G_D_Fin : G_D ≃ Fin (nD D) :=
    (Fintype.equivFin G_D).trans (Equiv.cast (congrArg Fin h_card_G_D))

  let alpha_min : α := Finset.min' Finset.univ Finset.univ_nonempty

  let f (x : α) : G_D :=
    let e := Classical.choose (h_H_idem x)
    let m_class := Finset.univ.filter (fun y => H_of y = H_of x)
    have hm_nonempty : m_class.Nonempty := ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, rfl⟩⟩
    let m := Finset.min' m_class hm_nonempty
    if h_mx : m < x then
      let val := e * σ.σ m x * e
      have h_val_in : val ∈ D ∧ ∃ e' ∈ D, e' * e' = e' ∧ GreenH val e' := sorry
      ⟨val, h_val_in⟩
    else
      have h_e_in : e ∈ D ∧ ∃ e' ∈ D, e' * e' = e' ∧ GreenH e e' := by
        have he_idem := Classical.choose_spec (h_H_idem x) |>.right
        have he_D : e ∈ D := sorry
        exact ⟨he_D, e, he_D, he_idem, green_h_refl e⟩
      ⟨e, h_e_in⟩

  let index_map := equiv_G_D_Fin.trans (Equiv.swap (equiv_G_D_Fin (f alpha_min)) max_rank)
  let s : Split α (nD D) := fun y => index_map (f y)

  use s
  constructor
  · change s alpha_min = Finset.max' Finset.univ Finset.univ_nonempty
    have h_min_eval : s alpha_min = max_rank := by
      dsimp only [s, index_map]
      rw [Equiv.trans_apply, Equiv.swap_apply_left]
    rw [h_min_eval]
    symm
    rw [Finset.max'_eq_iff]
    constructor
    · exact Finset.mem_univ _
    · intro y _
      apply Fin.le_iff_val_le_val.mpr
      
      have h_max_val : (max_rank : ℕ) = nD D - 1 := by
        have h_val : (max_rank : ℕ) = Fintype.card G_D - 1 := by simp [max_rank]
        rw [h_val, h_card_G_D]
        
      rw [h_max_val]
      exact Nat.le_pred_of_lt y.is_lt

  · intros x y hlt hsr
    unfold SplitRelation at hsr
    have h_s_eq := hsr.left
    
    have h_f_eq : f x = f y := by
      dsimp only [s] at h_s_eq
      exact Equiv.injective index_map h_s_eq
      
    have h_val_eq : (f x).val = (f y).val := congrArg Subtype.val h_f_eq

    have h_sigma_eq_idem : ∃ e ∈ D, e * e = e ∧ σ.σ x y = e := by
      sorry

    obtain ⟨e, _, he_idem, he_eq⟩ := h_sigma_eq_idem
    rw [he_eq]
    exact he_idem

end RegularDClassCase
