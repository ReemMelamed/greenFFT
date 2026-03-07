import Mathlib.Order.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

import Semigroup.Green

/-!
# The Factorisation Forest Theorem
-/

section SplitDefinitions

variable {S α : Type*} [Semigroup S] [LinearOrder α]

variable {h : ℕ}

structure MultiplicativeLabeling (S α : Type*) [Semigroup S] [LinearOrder α] where
  σ : α → α → S
  prop : ∀ x y z : α, x < y → y < z → σ x y * σ y z = σ x z

abbrev Split (α : Type*) (h : ℕ) := α → Fin h

def SplitRelation (s : Split α h) (x y : α) : Prop :=
  s x = s y ∧ ∀ z, min x y ≤ z → z ≤ max x y → s z ≤ s (min x y)

def IsNormalized [Fintype α] [Nonempty α] [Nonempty (Fin h)] (s : Split α h) : Prop :=
  let min_α := Finset.min' Finset.univ Finset.univ_nonempty
  s min_α = Finset.max' Finset.univ Finset.univ_nonempty

def IsRamsey (L : MultiplicativeLabeling S α) (s : Split α h) : Prop :=
  ∀ x y : α, x < y → SplitRelation s x y → L.σ x y * L.σ x y = L.σ x y

theorem split_relation_equiv (s : Split α h) : Equivalence (SplitRelation s) := by
  constructor <;> grind [SplitRelation]

end SplitDefinitions


section GroupCase

variable {G α : Type*} [Group G] [Fintype G] [LinearOrder α] [Fintype α] [Nonempty α]

open Classical in
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
    simp only [s, x₀]
    symm
    rw [Finset.max'_eq_iff]
    constructor
    · apply Finset.mem_univ
    · intro hy _
      apply Fin.le_iff_val_le_val.mpr
      simp only [max_rank]
      exact Nat.le_pred_of_lt hy.is_lt
  · intros x y hlt hsr
    unfold SplitRelation at hsr
    by_cases hx : x = x₀
    · subst hx
      have h_eq : s x₀ = s y := hsr.left
      have h_sx0 : s x₀ = max_rank := by simp only [s, ite_true]
      have h_y_ne : y ≠ x₀ := ne_of_gt hlt
      have h_sy : s y = index_in_enum (σ.σ x₀ y) := by simp only [s, h_y_ne, ite_false]
      rw [h_sx0, h_sy] at h_eq
      have h_map_1 : index_in_enum 1 = max_rank := by
        simp only [index_in_enum, Equiv.trans_apply, Equiv.swap_apply_left]
      rw [← h_map_1] at h_eq
      have h_val_1 : σ.σ x₀ y = 1 := Equiv.injective index_in_enum h_eq.symm
      simp only [h_val_1, mul_one]
    · have h_x0_lt_x : x₀ < x :=
        lt_of_le_of_ne (Finset.min'_le (.univ) x (Finset.mem_univ x)) (ne_comm.mp hx)
      have h_sx : s x = index_in_enum (σ.σ x₀ x) := by simp only [s, ne_of_gt h_x0_lt_x, ite_false]
      have h_x0_lt_y : x₀ < y := lt_trans h_x0_lt_x hlt
      have h_sy : s y = index_in_enum (σ.σ x₀ y) := by simp only [s, ne_of_gt h_x0_lt_y, ite_false]
      have h_s_eq : s x = s y := hsr.left
      rw [h_sx, h_sy] at h_s_eq
      have h_vals_eq : σ.σ x₀ x = σ.σ x₀ y := Equiv.injective index_in_enum h_s_eq
      have h_mult := σ.prop x₀ x y h_x0_lt_x hlt
      rw [← h_vals_eq] at h_mult
      have h_res : σ.σ x y = 1 := by
        have h_temp := congr_arg (fun g => (σ.σ x₀ x)⁻¹ * g) h_mult
        simp only [inv_mul_cancel_left, inv_mul_cancel] at h_temp
        exact h_temp
      simp only [h_res, mul_one]

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
  classical
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
    have h_val : σ_H.σ x y =
        ⟨σ.σ (x : α) (y : α), h_range (x : α) (y : α) x.property y.property hxy⟩ := by
      simp only [σ_H, σ_H_fun, hxy, dif_pos]
    have h_eq_in_S := congr_arg Subtype.val h_ramsey_xy
    simp only [h_val] at h_eq_in_S
    rw [← h_mul_eq] at h_eq_in_S
    exact h_eq_in_S

end HClassWrapper



section nD

variable {S : Type*} [Semigroup S] [Fintype S]

open Classical in
noncomputable def nD (D : Set S) : ℕ :=
  if IsRegularDClass D then
    (Finset.univ.filter (fun x =>
      x ∈ D ∧ ∃ e ∈ D, e * e = e ∧ IsGreenH x e
    )).card
  else
    1

theorem nD_pos (D : Set S) (hD : ∃ x, D = IsGreenD.eqvClass x) : 0 < nD D := by
  dsimp [nD]
  split_ifs with hReg
  · apply Finset.card_pos.mpr
    obtain ⟨e, heD, he_idem⟩ := (isRegularDClass_iff_exists_idempotent D hD).mp hReg
    use e
    simp only [Finset.mem_univ, Finset.mem_filter, true_and]
    refine ⟨heD, e, heD, he_idem, ?_⟩
    exact IsGreenH.refl e
  · exact Nat.zero_lt_one

instance (D : Set S) (hD : ∃ x, D = IsGreenD.eqvClass x) : Nonempty (Fin (nD D)) :=
  Fin.pos_iff_nonempty.mp (nD_pos D hD)

end nD



section RegularDClassCase

variable {S α : Type*} [Semigroup S] [Fintype S] [LinearOrder α] [Fintype α] [Nonempty α]

open Classical in
lemma simon_regular_d_case
    (σ : MultiplicativeLabeling S α)
    (D : Set S)
    (hD : ∃ x, D = IsGreenD.eqvClass x)
    (h_ne : Nonempty (Fin (nD D)) := Fin.pos_iff_nonempty.mp (nD_pos D hD))
    (hReg : IsRegularDClass D)
    (h_range : ∀ x y, x < y → σ.σ x y ∈ D) :
    ∃ (s : Split α (nD D)), IsNormalized s ∧ IsRamsey σ s := by
  obtain ⟨x₀, hx₀⟩ := hD
  have h_idem_L : ∀ a ∈ D, ∃ e ∈ IsGreenL.eqvClass a, e * e = e := by
    intro a ha
    obtain ⟨s, hs⟩ := hReg a ha
    use s * a
    constructor
    · constructor
      · right; use s
      · right; use a
        rw [← mul_assoc]
        exact hs.symm
    · have h_assoc : (s * a) * (s * a) = s * (a * s * a) := by simp [mul_assoc]
      rw [h_assoc, hs]
  have h_idem_R : ∀ a ∈ D, ∃ e ∈ IsGreenR.eqvClass a, e * e = e := by
    intro a ha
    obtain ⟨s, hs⟩ := hReg a ha
    use a * s
    constructor
    · constructor
      · right; use s
      · right; use a
        exact hs.symm
    · have h_assoc : (a * s) * (a * s) = (a * s * a) * s := by simp [mul_assoc]
      rw [h_assoc, hs]
  let is_max (x : α) : Prop := ∀ y, y ≤ x
  let is_min (x : α) : Prop := ∀ y, x ≤ y
  have exists_lt : ∀ {x : α}, ¬ is_min x → ∃ y, y < x := by
    intro x hx
    by_contra hc
    push_neg at hc
    exact hx hc
  have exists_gt : ∀ {x : α}, ¬ is_max x → ∃ y, x < y := by
    intro x hx
    by_contra hc
    push_neg at hc
    exact hx hc
  let get_lt (x : α) (h : ¬ is_min x) : α := Classical.choose (exists_lt h)
  have get_lt_prop : ∀ x h, get_lt x h < x := fun x h => Classical.choose_spec (exists_lt h)
  let get_gt (x : α) (h : ¬ is_max x) : α := Classical.choose (exists_gt h)
  have get_gt_prop : ∀ x h, x < get_gt x h := fun x h => Classical.choose_spec (exists_gt h)
  let L_of (x : α) : Set S :=
    if h_min : is_min x then
      if h_max : is_max x then
        IsGreenL.eqvClass x₀
      else
        have ha_D : σ.σ x (get_gt x h_max) ∈ D := h_range x _ (get_gt_prop x h_max)
        IsGreenL.eqvClass (Classical.choose (h_idem_R (σ.σ x (get_gt x h_max)) ha_D))
    else
      IsGreenL.eqvClass (σ.σ (get_lt x h_min) x)
  have h_L_well : ∀ x y1 y2 (h_not_min : ¬ is_min x) (hy1 : y1 < x) (hy2 : y2 < x),
      IsGreenL.eqvClass (σ.σ y1 x) = IsGreenL.eqvClass (σ.σ y2 x) := by
    intro x y1 y2 h_not_min hy1 hy2
    wlog h_le : y1 ≤ y2 generalizing y1 y2 hy1 hy2
    · exact (this y2 y1 hy2 hy1 (le_of_lt (not_le.mp h_le))).symm
    · rcases h_le.eq_or_lt with rfl | h_lt
      · rfl
      · have h_prod : σ.σ y1 x = σ.σ y1 y2 * σ.σ y2 x := (σ.prop y1 y2 x h_lt hy2).symm
        have h12 : σ.σ y1 y2 ∈ D := h_range y1 y2 h_lt
        have h2x : σ.σ y2 x ∈ D := h_range y2 x hy2
        have h1x : σ.σ y1 x ∈ D := h_range y1 x hy1
        have hL_raw :=
          (mul_mem_isGreenD_eqvClass_properties ⟨x₀, hx₀⟩ (σ.σ y1 y2) (σ.σ y2 x) h12 h2x
          (h_prod ▸ h1x)).1.2
        have hL : IsGreenL (σ.σ y2 x) (σ.σ y1 x) := h_prod ▸ hL_raw
        ext z
        constructor
        · intro hz; exact IsGreenL.trans hz (IsGreenL.symm hL)
        · intro hz; exact IsGreenL.trans hz hL
  let R_of (x : α) : Set S :=
    if h_max : is_max x then
      if h_min : is_min x then
        have ha_D : x₀ ∈ D := by rw [hx₀]; exact IsGreenD.refl x₀
        IsGreenR.eqvClass (Classical.choose (h_idem_L x₀ ha_D))
      else
        have ha_D : σ.σ (get_lt x h_min) x ∈ D := h_range _ x (get_lt_prop x h_min)
        IsGreenR.eqvClass (Classical.choose (h_idem_L (σ.σ (get_lt x h_min) x) ha_D))
    else
      IsGreenR.eqvClass (σ.σ x (get_gt x h_max))
  have h_R_well : ∀ x y1 y2 (h_not_max : ¬ is_max x) (hy1 : x < y1) (hy2 : x < y2),
      IsGreenR.eqvClass (σ.σ x y1) = IsGreenR.eqvClass (σ.σ x y2) := by
    intro x y1 y2 h_not_max hy1 hy2
    wlog h_le : y1 ≤ y2 generalizing y1 y2 hy1 hy2
    · exact (this y2 y1 hy2 hy1 (le_of_lt (not_le.mp h_le))).symm
    · rcases h_le.eq_or_lt with rfl | h_lt
      · rfl
      · have h_prod : σ.σ x y1 * σ.σ y1 y2 = σ.σ x y2 := σ.prop x y1 y2 hy1 h_lt
        have hx1 : σ.σ x y1 ∈ D := h_range x y1 hy1
        have h12 : σ.σ y1 y2 ∈ D := h_range y1 y2 h_lt
        have hx2 : σ.σ x y2 ∈ D := h_range x y2 hy2
        have hR_raw :=
          (mul_mem_isGreenD_eqvClass_properties ⟨x₀, hx₀⟩ (σ.σ x y1) (σ.σ y1 y2) hx1 h12
          (h_prod.symm ▸ hx2)).1.1
        have hR : IsGreenR (σ.σ x y1) (σ.σ x y2) := h_prod ▸ hR_raw
        ext z
        constructor
        · intro hz; exact IsGreenR.trans hz hR
        · intro hz; exact IsGreenR.trans hz (IsGreenR.symm hR)
  let H_of (x : α) : Set S := L_of x ∩ R_of x
  have h_H_idem : ∀ (x : α), ∃ e : S, e ∈ H_of x ∧ e * e = e := by
    intro x
    dsimp [H_of]
    by_cases h_min : is_min x
    · by_cases h_max : is_max x
      · have ha_D : x₀ ∈ D := by rw [hx₀]; exact IsGreenD.refl x₀
        let ex : S := Classical.choose (h_idem_L x₀ ha_D)
        have he_prop := Classical.choose_spec (h_idem_L x₀ ha_D)
        use ex
        refine ⟨⟨?_, ?_⟩, he_prop.right⟩
        · simp only [L_of, h_min, h_max, dite_true]
          exact he_prop.left
        · simp only [R_of, h_max, h_min, dite_true]
          exact IsGreenR.refl ex
      · have ha_D : σ.σ x (get_gt x h_max) ∈ D := h_range x _ (get_gt_prop x h_max)
        let ex : S := Classical.choose (h_idem_R (σ.σ x (get_gt x h_max)) ha_D)
        have he_prop := Classical.choose_spec (h_idem_R _ ha_D)
        use ex
        refine ⟨⟨?_, ?_⟩, he_prop.right⟩
        · simp only [L_of, h_min, h_max, dite_true, dite_false]
          exact IsGreenL.refl ex
        · simp only [R_of, h_max, dite_false]
          exact he_prop.left
    · by_cases h_max : is_max x
      · have ha_D : σ.σ (get_lt x h_min) x ∈ D := h_range _ x (get_lt_prop x h_min)
        let ex : S := Classical.choose (h_idem_L (σ.σ (get_lt x h_min) x) ha_D)
        have he_prop := Classical.choose_spec (h_idem_L _ ha_D)
        use ex
        refine ⟨⟨?_, ?_⟩, he_prop.right⟩
        · simp only [L_of, h_min, dite_false]
          exact he_prop.left
        · simp only [R_of, h_max, h_min, dite_true, dite_false]
          exact IsGreenR.refl ex
      · have ha : σ.σ (get_lt x h_min) x ∈ D := h_range _ _ (get_lt_prop x h_min)
        have hb : σ.σ x (get_gt x h_max) ∈ D := h_range _ _ (get_gt_prop x h_max)
        have hab : σ.σ (get_lt x h_min) x * σ.σ x (get_gt x h_max) ∈ D := by
          rw [σ.prop _ _ _ (get_lt_prop x h_min) (get_gt_prop x h_max)]
          exact h_range _ _ (lt_trans (get_lt_prop x h_min) (get_gt_prop x h_max))
        obtain ⟨_, ⟨ex, _, he_idem, hLe, hRe⟩⟩ := mul_mem_isGreenD_eqvClass_properties ⟨x₀, hx₀⟩ _ _ ha hb hab
        use ex
        refine ⟨⟨?_, ?_⟩, he_idem⟩
        · simp only [L_of, h_min, dite_false]
          exact IsGreenL.symm hLe
        · simp only [R_of, h_max, dite_false]
          exact IsGreenR.symm hRe
  choose e he_H he_idem using h_H_idem
  have h_H_eq_class : ∀ (z : α), H_of z = IsGreenH.eqvClass (e z) := by
    intro z
    ext w
    constructor
    · rintro ⟨hwL, hwR⟩
      have h1 : e z ∈ L_of z := (he_H z).1
      have h2 : e z ∈ R_of z := (he_H z).2
      have he_L_rel : IsGreenL (e z) w := by
        dsimp only [L_of] at h1 hwL
        split_ifs at h1 hwL
        · exact IsGreenL.trans h1 (IsGreenL.symm hwL)
        · exact IsGreenL.trans h1 (IsGreenL.symm hwL)
        · exact IsGreenL.trans h1 (IsGreenL.symm hwL)
      have he_R_rel : IsGreenR (e z) w := by
        dsimp only [R_of] at h2 hwR
        split_ifs at h2 hwR
        · exact IsGreenR.trans h2 (IsGreenR.symm hwR)
        · exact IsGreenR.trans h2 (IsGreenR.symm hwR)
        · exact IsGreenR.trans h2 (IsGreenR.symm hwR)
      exact ⟨IsGreenL.symm he_L_rel, IsGreenR.symm he_R_rel⟩
    · rintro ⟨hwL, hwR⟩
      have h1 : e z ∈ L_of z := (he_H z).1
      have h2 : e z ∈ R_of z := (he_H z).2
      have hw_L_mem : w ∈ L_of z := by
        dsimp only [L_of] at h1 ⊢
        split_ifs at h1 ⊢
        · exact IsGreenL.trans hwL h1
        · exact IsGreenL.trans hwL h1
        · exact IsGreenL.trans hwL h1
      have hw_R_mem : w ∈ R_of z := by
        dsimp only [R_of] at h2 ⊢
        split_ifs at h2 ⊢
        · exact IsGreenR.trans hwR h2
        · exact IsGreenR.trans hwR h2
        · exact IsGreenR.trans hwR h2
      exact ⟨hw_L_mem, hw_R_mem⟩
  have H_idem_eq : ∀ (a b : S), IsGreenH a b → a * a = a → b * b = b → a = b := by
    intro a b hab ha hb
    have h_ab_eq_b : a * b = b := by
      rcases hab.right.right with rfl | ⟨x, hx⟩
      · exact hb
      · calc a * b = a * (a * x) := by rw [hx]
          _ = (a * a) * x := (mul_assoc a a x).symm
          _ = a * x := by rw [ha]
          _ = b := hx.symm
    have h_ab_eq_a : a * b = a := by
      rcases hab.left.left with rfl | ⟨y, hy⟩
      · exact ha
      · calc a * b = (y * b) * b := by rw [hy]
          _ = y * (b * b) := mul_assoc y b b
          _ = y * b := by rw [hb]
          _ = a := hy.symm
    rw [← h_ab_eq_a, h_ab_eq_b]
  have h_H_id : ∀ (a e' : S), IsGreenH a e' → e' * e' = e' → a * e' = a ∧ e' * a = a := by
    intro a e' hae he'
    constructor
    · rcases hae.left.left with rfl | ⟨w, hw⟩
      · exact he'
      · calc a * e' = (w * e') * e' := by rw [hw]
          _ = w * (e' * e') := mul_assoc w e' e'
          _ = w * e' := by rw [he']
          _ = a := hw.symm
    · rcases hae.right.left with rfl | ⟨w, hw⟩
      · exact he'
      · calc e' * a = e' * (e' * w) := by rw [hw]
          _ = (e' * e') * w := (mul_assoc e' e' w).symm
          _ = e' * w := by rw [he']
          _ = a := hw.symm
  have h_sig_props : ∀ (z mz : α), mz < z → H_of mz = H_of z →
      e z * σ.σ mz z * e z = σ.σ mz z ∧ IsGreenH (σ.σ mz z) (e z) := by
    intro z mz h_mz hm_H
    have he_z_idem : e z * e z = e z := he_idem z
    have h_not_min_z : ¬ is_min z := fun h => lt_irrefl mz (lt_of_lt_of_le h_mz (h mz))
    have h_L_mz : L_of z = IsGreenL.eqvClass (σ.σ mz z) := by
      dsimp only [L_of]
      rw [dif_neg h_not_min_z]
      exact h_L_well z (get_lt z h_not_min_z) mz h_not_min_z (get_lt_prop z h_not_min_z) h_mz
    have he_L_mz_z : IsGreenL (e z) (σ.σ mz z) := by
      have h1 : e z ∈ L_of z := (he_H z).1
      rwa [h_L_mz] at h1
    have h_not_max_m : ¬ is_max mz := fun h => lt_irrefl z (lt_of_le_of_lt (h z) h_mz)
    have h_R_mz : R_of mz = IsGreenR.eqvClass (σ.σ mz z) := by
      dsimp only [R_of]
      rw [dif_neg h_not_max_m]
      exact h_R_well mz (get_gt mz h_not_max_m) z h_not_max_m (get_gt_prop mz h_not_max_m) h_mz
    have he_R_mz_z : IsGreenR (e z) (σ.σ mz z) := by
      have hz_in_H : e z ∈ H_of mz := hm_H ▸ he_H z
      have h1 : e z ∈ R_of mz := hz_in_H.2
      rwa [h_R_mz] at h1
    have he_H_mz_z : IsGreenH (e z) (σ.σ mz z) := ⟨he_L_mz_z, he_R_mz_z⟩
    have h_sig_H_e : IsGreenH (σ.σ mz z) (e z) := IsGreenH.symm he_H_mz_z
    have hid := h_H_id (σ.σ mz z) (e z) h_sig_H_e he_z_idem
    have h_simp : e z * σ.σ mz z * e z = σ.σ mz z := by
      calc e z * σ.σ mz z * e z = (e z * σ.σ mz z) * e z := by simp only [mul_assoc]
        _ = σ.σ mz z * e z := by rw [hid.2]
        _ = σ.σ mz z := hid.1
    exact ⟨h_simp, h_sig_H_e⟩
  let G_D := { y : S // y ∈ D ∧ ∃ e ∈ D, e * e = e ∧ IsGreenH y e }
  have h_card_G_D : Fintype.card G_D = nD D := by
    dsimp [nD]
    rw [if_pos hReg]
    exact Fintype.card_subtype (fun y => y ∈ D ∧ ∃ e ∈ D, e * e = e ∧ IsGreenH y e)
  have h_card_pos : 0 < Fintype.card G_D := by
    rw [h_card_G_D]
    exact Fin.pos_iff_nonempty.mpr h_ne
  haveI h_nonempty_GD : Nonempty G_D := Fintype.card_pos_iff.mp h_card_pos
  have h_size_cast : Fintype.card G_D - 1 + 1 = Fintype.card G_D := Nat.sub_add_cancel h_card_pos
  let max_rank : Fin (nD D) :=
    Fin.cast h_card_G_D (Fin.cast h_size_cast (Fin.last (Fintype.card G_D - 1)))
  let equiv_G_D_Fin : G_D ≃ Fin (nD D) :=
    (Fintype.equivFin G_D).trans (Equiv.cast (congrArg Fin h_card_G_D))
  let alpha_min : α := Finset.min' Finset.univ Finset.univ_nonempty
  let f (x : α) : G_D :=
    let m_class := Finset.univ.filter (fun y => H_of y = H_of x)
    have hm_nonempty : m_class.Nonempty := ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, rfl⟩⟩
    let m := Finset.min' m_class hm_nonempty
    if h_mx : m < x then
      let val := e x * σ.σ m x * e x
      have h_val_in : val ∈ D ∧ ∃ e' ∈ D, e' * e' = e' ∧ IsGreenH val e' := by
        have he_idem_x : e x * e x = e x := he_idem x
        have hm_in := Finset.min'_mem m_class hm_nonempty
        have hm_H : H_of m = H_of x := (Finset.mem_filter.mp hm_in).2
        have h_not_min_x : ¬ is_min x := fun h => lt_irrefl m (lt_of_lt_of_le h_mx (h m))
        have h_L_mx : L_of x = IsGreenL.eqvClass (σ.σ m x) := by
          dsimp only [L_of]
          rw [dif_neg h_not_min_x]
          exact h_L_well x (get_lt x h_not_min_x) m h_not_min_x (get_lt_prop x h_not_min_x) h_mx
        have he_L_sig : IsGreenL (e x) (σ.σ m x) := by
          have h1 : e x ∈ L_of x := (he_H x).1
          rwa [h_L_mx] at h1
        have h_not_max_m : ¬ is_max m := fun h => lt_irrefl x (lt_of_le_of_lt (h x) h_mx)
        have h_R_m : R_of m = IsGreenR.eqvClass (σ.σ m x) := by
          dsimp only [R_of]
          rw [dif_neg h_not_max_m]
          exact h_R_well m (get_gt m h_not_max_m) x h_not_max_m (get_gt_prop m h_not_max_m) h_mx
        have he_R_sig : IsGreenR (e x) (σ.σ m x) := by
          have hx_in_H : e x ∈ H_of m := hm_H ▸ he_H x
          have h1 : e x ∈ R_of m := hx_in_H.2
          rwa [h_R_m] at h1
        have he_H_sig : IsGreenH (e x) (σ.σ m x) := ⟨he_L_sig, he_R_sig⟩
        have h_sig_H_e : IsGreenH (σ.σ m x) (e x) := IsGreenH.symm he_H_sig
        have h_class_eq : ∃ a, IsGreenH.eqvClass (e x) = IsGreenH.eqvClass a := ⟨e x, rfl⟩
        have h_group_or := is_group_isGreenH_eqvClass_iff_idempotent (IsGreenH.eqvClass (e x)) h_class_eq
        have h_group : ∀ u v, u ∈ IsGreenH.eqvClass (e x) → v ∈ IsGreenH.eqvClass (e x) → u * v ∈ IsGreenH.eqvClass (e x) := by
          rcases h_group_or with h_empty | ⟨e', he'H, he'idem, h_mul⟩
          · have h_ee_not := h_empty (e x) (e x) (IsGreenH.refl (e x)) (IsGreenH.refl (e x))
            rw [he_idem_x] at h_ee_not
            exact False.elim (h_ee_not (IsGreenH.refl (e x)))
          · exact h_mul
        have h_sig_He : σ.σ m x ∈ IsGreenH.eqvClass (e x) := h_sig_H_e
        have he_He : e x ∈ IsGreenH.eqvClass (e x) := IsGreenH.refl (e x)
        have h_val_He : val ∈ IsGreenH.eqvClass (e x) := by
          dsimp only [val]
          have h1 := h_group (e x) (σ.σ m x) he_He h_sig_He
          exact h_group (e x * σ.σ m x) (e x) h1 he_He
        have h_val_H_e : IsGreenH val (e x) := h_val_He
        have h_sig_D : σ.σ m x ∈ D := h_range m x h_mx
        have he_D_sig : IsGreenD (e x) (σ.σ m x) := ⟨e x, IsGreenL.refl (e x), he_H_sig.right⟩
        have he_D : e x ∈ D := by
          rw [hx₀] at h_sig_D ⊢
          exact IsGreenD.trans he_D_sig h_sig_D
        have hval_D_e : IsGreenD val (e x) := ⟨val, IsGreenL.refl val, h_val_H_e.right⟩
        have h_val_D : val ∈ D := by
          rw [hx₀] at he_D ⊢
          exact IsGreenD.trans hval_D_e he_D
        exact ⟨h_val_D, e x, he_D, he_idem_x, h_val_H_e⟩
      ⟨val, h_val_in⟩
    else
      have h_e_in : e x ∈ D ∧ ∃ e' ∈ D, e' * e' = e' ∧ IsGreenH (e x) e' := by
        have he_idem_x := he_idem x
        have he_D : e x ∈ D := by
          have he_L : e x ∈ L_of x := (he_H x).1
          by_cases h_min : is_min x
          · by_cases h_max : is_max x
            · dsimp only [L_of] at he_L
              rw [dif_pos h_min, dif_pos h_max] at he_L
              rw [hx₀]
              exact ⟨x₀, he_L, IsGreenR.refl x₀⟩
            · let y' := get_gt x h_max
              have ha_D : σ.σ x y' ∈ D := h_range x y' (get_gt_prop x h_max)
              dsimp only [L_of] at he_L
              rw [dif_pos h_min, dif_neg h_max] at he_L
              let e_R : S := Classical.choose (h_idem_R (σ.σ x y') ha_D)
              have he_R_prop := Classical.choose_spec (h_idem_R _ ha_D)
              rw [hx₀] at ha_D ⊢
              have hD_e_sig : IsGreenD (e x) (σ.σ x y') := ⟨e_R, he_L, he_R_prop.left⟩
              exact IsGreenD.trans hD_e_sig ha_D
          · let y' := get_lt x h_min
            dsimp only [L_of] at he_L
            rw [dif_neg h_min] at he_L
            have ha_D : σ.σ y' x ∈ D := h_range y' x (get_lt_prop x h_min)
            rw [hx₀] at ha_D ⊢
            have hD_e_sig : IsGreenD (e x) (σ.σ y' x) := ⟨σ.σ y' x, he_L, IsGreenR.refl _⟩
            exact IsGreenD.trans hD_e_sig ha_D
        exact ⟨he_D, e x, he_D, he_idem_x, IsGreenH.refl (e x)⟩
      ⟨e x, h_e_in⟩
  have h_fz_H_ez : ∀ (z : α), IsGreenH (f z).val (e z) := by
    intro z
    let m_class := Finset.univ.filter (fun w => H_of w = H_of z)
    have hm_nonempty : m_class.Nonempty := ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ z, rfl⟩⟩
    let mz := Finset.min' m_class hm_nonempty
    have hm_in := Finset.min'_mem m_class hm_nonempty
    have hm_H : H_of mz = H_of z := (Finset.mem_filter.mp hm_in).2
    have h_val : (f z).val = if h_lt : mz < z then e z * σ.σ mz z * e z else e z := by
      dsimp only [f]; split_ifs <;> rfl
    rw [h_val]
    split_ifs with h_mz
    · have h_props := h_sig_props z mz h_mz hm_H
      rw [h_props.1]
      exact h_props.2
    · exact IsGreenH.refl (e z)
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
        simp only [max_rank, Fin.val_cast, Fin.val_last]
        rw [h_card_G_D]
      rw [h_max_val]
      exact Nat.le_pred_of_lt y.is_lt
  · intros x y hlt hsr
    unfold SplitRelation at hsr
    have h_s_eq := hsr.left
    have h_f_eq : f x = f y := by
      dsimp only [s] at h_s_eq
      exact Equiv.injective index_map h_s_eq
    have h_val_eq : (f x).val = (f y).val := congrArg Subtype.val h_f_eq
    have h_sigma_eq_idem : ∃ e_id ∈ D, e_id * e_id = e_id ∧ σ.σ x y = e_id := by
      have he_D : e x ∈ D := by
        have he_L : e x ∈ L_of x := (he_H x).1
        by_cases h_min : is_min x
        · by_cases h_max : is_max x
          · dsimp only [L_of] at he_L
            rw [dif_pos h_min, dif_pos h_max] at he_L
            rw [hx₀]
            exact ⟨x₀, he_L, IsGreenR.refl x₀⟩
          · let y' := get_gt x h_max
            have ha_D : σ.σ x y' ∈ D := h_range x y' (get_gt_prop x h_max)
            dsimp only [L_of] at he_L
            rw [dif_pos h_min, dif_neg h_max] at he_L
            let e_R : S := Classical.choose (h_idem_R (σ.σ x y') ha_D)
            have he_R_prop := Classical.choose_spec (h_idem_R _ ha_D)
            rw [hx₀] at ha_D ⊢
            have hD_e_sig : IsGreenD (e x) (σ.σ x y') := ⟨e_R, he_L, he_R_prop.left⟩
            exact IsGreenD.trans hD_e_sig ha_D
        · let y' := get_lt x h_min
          dsimp only [L_of] at he_L
          rw [dif_neg h_min] at he_L
          have ha_D : σ.σ y' x ∈ D := h_range y' x (get_lt_prop x h_min)
          rw [hx₀] at ha_D ⊢
          have hD_e_sig : IsGreenD (e x) (σ.σ y' x) := ⟨σ.σ y' x, he_L, IsGreenR.refl _⟩
          exact IsGreenD.trans hD_e_sig ha_D
      have h_fz_H_e : IsGreenH (f x).val (e x) := h_fz_H_ez x
      have h_fy_H_ey : IsGreenH (f y).val (e y) := h_fz_H_ez y
      have he_H_ey : IsGreenH (e x) (e y) := by
        have h1 : IsGreenH (e x) (f x).val := IsGreenH.symm h_fz_H_e
        exact IsGreenH.trans h1 (h_val_eq ▸ h_fy_H_ey)
      have he_eq_ey : e x = e y :=
        H_idem_eq (e x) (e y) he_H_ey (he_idem x) (he_idem y)
      let m_class_x := Finset.univ.filter (fun z => H_of z = H_of x)
      let m_class_y := Finset.univ.filter (fun z => H_of z = H_of y)
      have hm_nonempty_x : m_class_x.Nonempty := ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, rfl⟩⟩
      have hm_nonempty_y : m_class_y.Nonempty := ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ y, rfl⟩⟩
      let mx := Finset.min' m_class_x hm_nonempty_x
      let my := Finset.min' m_class_y hm_nonempty_y
      have h_same_H : H_of x = H_of y := by
        rw [h_H_eq_class x, h_H_eq_class y, he_eq_ey]
      have h_mx_eq_my : mx = my := by
        have h_class_eq : m_class_x = m_class_y := by
          ext z
          simp only [m_class_x, m_class_y, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨fun h => h.trans h_same_H, fun h => h.trans h_same_H.symm⟩
        apply le_antisymm
        · have h_my_in_x : my ∈ m_class_x := by rw [h_class_eq]; exact Finset.min'_mem m_class_y hm_nonempty_y
          exact Finset.min'_le m_class_x my h_my_in_x
        · have h_mx_in_y : mx ∈ m_class_y := by rw [← h_class_eq]; exact Finset.min'_mem m_class_x hm_nonempty_x
          exact Finset.min'_le m_class_y mx h_mx_in_y
      have h_ese_eq_e : e x * σ.σ x y * e x = e x := by
        by_cases h_mx : mx < x
        · have h_mem_x := Finset.min'_mem m_class_x hm_nonempty_x
          have hm_H : H_of mx = H_of x := (Finset.mem_filter.mp h_mem_x).2
          have h_not_min_x : ¬ is_min x := fun h => lt_irrefl mx (lt_of_lt_of_le h_mx (h mx))
          have h_L_mx : L_of x = IsGreenL.eqvClass (σ.σ mx x) := by
            dsimp only [L_of]
            rw [dif_neg h_not_min_x]
            exact h_L_well x (get_lt x h_not_min_x) mx h_not_min_x (get_lt_prop x h_not_min_x) h_mx
          have he_L_sig : IsGreenL (e x) (σ.σ mx x) := by
            have h1 : e x ∈ L_of x := (he_H x).1
            rwa [h_L_mx] at h1
          have h_not_max_mx : ¬ is_max mx := fun h => lt_irrefl x (lt_of_le_of_lt (h x) h_mx)
          have h_R_mx : R_of mx = IsGreenR.eqvClass (σ.σ mx x) := by
            dsimp only [R_of]
            rw [dif_neg h_not_max_mx]
            exact h_R_well mx (get_gt mx h_not_max_mx) x h_not_max_mx (get_gt_prop mx h_not_max_mx) h_mx
          have he_R_sig : IsGreenR (e x) (σ.σ mx x) := by
            have hx_in_H : e x ∈ H_of mx := hm_H ▸ he_H x
            have h1 : e x ∈ R_of mx := hx_in_H.2
            rwa [h_R_mx] at h1
          have he_H_sig_mx : IsGreenH (e x) (σ.σ mx x) := ⟨he_L_sig, he_R_sig⟩
          have h_sig_H_e_mx : IsGreenH (σ.σ mx x) (e x) := IsGreenH.symm he_H_sig_mx
          have hid_mx := h_H_id (σ.σ mx x) (e x) h_sig_H_e_mx (he_idem x)
          have h_val_x : (f x).val = if h_lt : mx < x then e x * σ.σ mx x * e x else e x := by
            dsimp only [f]; split_ifs <;> rfl
          have h_fx : (f x).val = σ.σ mx x := by
            rw [h_val_x, dif_pos h_mx]
            calc e x * σ.σ mx x * e x = (e x * σ.σ mx x) * e x := by simp only [mul_assoc]
              _ = σ.σ mx x * e x := by rw [hid_mx.2]
              _ = σ.σ mx x := hid_mx.1
          have h_my : my < y := by rw [← h_mx_eq_my]; exact lt_trans h_mx hlt
          have h_mem_y := Finset.min'_mem m_class_y hm_nonempty_y
          have hm_Hy : H_of my = H_of y := (Finset.mem_filter.mp h_mem_y).2
          have h_not_min_y : ¬ is_min y := fun h => lt_irrefl my (lt_of_lt_of_le h_my (h my))
          have h_L_my : L_of y = IsGreenL.eqvClass (σ.σ my y) := by
            dsimp only [L_of]
            rw [dif_neg h_not_min_y]
            exact h_L_well y (get_lt y h_not_min_y) my h_not_min_y (get_lt_prop y h_not_min_y) h_my
          have hey_L_sig : IsGreenL (e y) (σ.σ my y) := by
            have h1 : e y ∈ L_of y := (he_H y).1
            rwa [h_L_my] at h1
          have h_not_max_my : ¬ is_max my := fun h => lt_irrefl y (lt_of_le_of_lt (h y) h_my)
          have h_R_my : R_of my = IsGreenR.eqvClass (σ.σ my y) := by
            dsimp only [R_of]
            rw [dif_neg h_not_max_my]
            exact h_R_well my (get_gt my h_not_max_my) y h_not_max_my (get_gt_prop my h_not_max_my) h_my
          have hey_R_sig : IsGreenR (e y) (σ.σ my y) := by
            have hy_in_H : e y ∈ H_of my := hm_Hy ▸ he_H y
            have h1 : e y ∈ R_of my := hy_in_H.2
            rwa [h_R_my] at h1
          have he_H_sig_my : IsGreenH (e y) (σ.σ my y) := ⟨hey_L_sig, hey_R_sig⟩
          have h_sig_H_e_my : IsGreenH (σ.σ my y) (e y) := IsGreenH.symm he_H_sig_my
          have hid_my := h_H_id (σ.σ my y) (e y) h_sig_H_e_my (he_idem y)
          have h_val_y : (f y).val = if h_lt : my < y then e y * σ.σ my y * e y else e y := by
            dsimp only [f]; split_ifs <;> rfl
          have h_fy : (f y).val = σ.σ my y := by
            rw [h_val_y, dif_pos h_my]
            calc e y * σ.σ my y * e y = (e y * σ.σ my y) * e y := by simp only [mul_assoc]
              _ = σ.σ my y * e y := by rw [hid_my.2]
              _ = σ.σ my y := hid_my.1
          have h_v_eq : σ.σ mx x * σ.σ x y * e x = σ.σ mx x := by
            calc σ.σ mx x * σ.σ x y * e x = (e x * σ.σ mx x) * σ.σ x y * e x := congrArg (fun w => w * σ.σ x y * e x) hid_mx.2.symm
              _ = e x * (σ.σ mx x * σ.σ x y) * e x := by simp only [mul_assoc]
              _ = e x * σ.σ mx y * e x := by rw [← σ.prop mx x y h_mx hlt]
              _ = e y * σ.σ my y * e y := by rw [he_eq_ey, h_mx_eq_my]
              _ = (e y * σ.σ my y) * e y := by simp only [mul_assoc]
              _ = σ.σ my y * e y := by rw [hid_my.2]
              _ = σ.σ my y := hid_my.1
              _ = (f y).val := h_fy.symm
              _ = (f x).val := h_val_eq.symm
              _ = σ.σ mx x := h_fx
          rcases he_L_sig.left with heq | ⟨u, hu⟩
          · calc e x * σ.σ x y * e x = σ.σ mx x * σ.σ x y * e x := by rw [heq]
              _ = σ.σ mx x := h_v_eq
              _ = e x := heq.symm
          · calc e x * σ.σ x y * e x = (u * σ.σ mx x) * σ.σ x y * e x := by rw [hu]
              _ = u * (σ.σ mx x * σ.σ x y * e x) := by simp only [mul_assoc]
              _ = u * σ.σ mx x := by rw [h_v_eq]
              _ = e x := hu.symm
        · have h_x_le_mx : x ≤ mx := not_lt.mp h_mx
          have h_mx_le_x : mx ≤ x := Finset.min'_le m_class_x x (Finset.mem_filter.mpr ⟨Finset.mem_univ x, rfl⟩)
          have h_mx_eq : mx = x := le_antisymm h_mx_le_x h_x_le_mx
          have h_val_x : (f x).val = if h_lt : mx < x then e x * σ.σ mx x * e x else e x := by
            dsimp only [f]; split_ifs <;> rfl
          have h_fx : (f x).val = e x := by
            rw [h_val_x, dif_neg h_mx]
          have h_my : my < y := by rw [← h_mx_eq_my, h_mx_eq]; exact hlt
          have h_mem_y := Finset.min'_mem m_class_y hm_nonempty_y
          have hm_Hy : H_of my = H_of y := (Finset.mem_filter.mp h_mem_y).2
          have h_not_min_y : ¬ is_min y := fun h => lt_irrefl my (lt_of_lt_of_le h_my (h my))
          have h_L_my : L_of y = IsGreenL.eqvClass (σ.σ my y) := by
            dsimp only [L_of]
            rw [dif_neg h_not_min_y]
            exact h_L_well y (get_lt y h_not_min_y) my h_not_min_y (get_lt_prop y h_not_min_y) h_my
          have hey_L_sig : IsGreenL (e y) (σ.σ my y) := by
            have h1 : e y ∈ L_of y := (he_H y).1
            rwa [h_L_my] at h1
          have h_not_max_my : ¬ is_max my := fun h => lt_irrefl y (lt_of_le_of_lt (h y) h_my)
          have h_R_my : R_of my = IsGreenR.eqvClass (σ.σ my y) := by
            dsimp only [R_of]
            rw [dif_neg h_not_max_my]
            exact h_R_well my (get_gt my h_not_max_my) y h_not_max_my (get_gt_prop my h_not_max_my) h_my
          have hey_R_sig : IsGreenR (e y) (σ.σ my y) := by
            have hy_in_H : e y ∈ H_of my := hm_Hy ▸ he_H y
            have h1 : e y ∈ R_of my := hy_in_H.2
            rwa [h_R_my] at h1
          have he_H_sig_my : IsGreenH (e y) (σ.σ my y) := ⟨hey_L_sig, hey_R_sig⟩
          have h_sig_H_e_my : IsGreenH (σ.σ my y) (e y) := IsGreenH.symm he_H_sig_my
          have hid_my := h_H_id (σ.σ my y) (e y) h_sig_H_e_my (he_idem y)
          have h_val_y : (f y).val = if h_lt : my < y then e y * σ.σ my y * e y else e y := by
            dsimp only [f]; split_ifs <;> rfl
          have h_fy : (f y).val = σ.σ my y := by
            rw [h_val_y, dif_pos h_my]
            calc e y * σ.σ my y * e y = (e y * σ.σ my y) * e y := by simp only [mul_assoc]
              _ = σ.σ my y * e y := by rw [hid_my.2]
              _ = σ.σ my y := hid_my.1
          calc e x * σ.σ x y * e x = e y * σ.σ my y * e y := by rw [← he_eq_ey, ← h_mx_eq_my, h_mx_eq]
            _ = (e y * σ.σ my y) * e y := by simp only [mul_assoc]
            _ = σ.σ my y * e y := by rw [hid_my.2]
            _ = σ.σ my y := hid_my.1
            _ = (f y).val := h_fy.symm
            _ = (f x).val := h_val_eq.symm
            _ = e x := h_fx
      have h_sig_H : IsGreenH (σ.σ x y) (e x) := by
        have h_not_min_y : ¬ is_min y := fun h => lt_irrefl x (lt_of_lt_of_le hlt (h x))
        have h_L_y : L_of y = IsGreenL.eqvClass (σ.σ x y) := by
          dsimp only [L_of]
          rw [dif_neg h_not_min_y]
          exact h_L_well y (get_lt y h_not_min_y) x h_not_min_y (get_lt_prop y h_not_min_y) hlt
        have hex_in_Hy : e x ∈ H_of y := h_same_H ▸ he_H x
        have he_L : e x ∈ L_of y := hex_in_Hy.1
        have he_L_mem : IsGreenL (e x) (σ.σ x y) := by rwa [h_L_y] at he_L
        have h_not_max_x : ¬ is_max x := fun h => lt_irrefl y (lt_of_le_of_lt (h y) hlt)
        have h_R_x : R_of x = IsGreenR.eqvClass (σ.σ x y) := by
          dsimp only [R_of]
          rw [dif_neg h_not_max_x]
          exact h_R_well x (get_gt x h_not_max_x) y h_not_max_x (get_gt_prop x h_not_max_x) hlt
        have he_R : e x ∈ R_of x := (he_H x).2
        have he_R_mem : IsGreenR (e x) (σ.σ x y) := by rwa [h_R_x] at he_R
        exact IsGreenH.symm ⟨he_L_mem, he_R_mem⟩
      have h_final_sigma : σ.σ x y = e x := by
        have h_sig_id := h_H_id (σ.σ x y) (e x) h_sig_H (he_idem x)
        calc σ.σ x y = e x * σ.σ x y := h_sig_id.2.symm
          _ = e x * (σ.σ x y * e x) := congrArg (fun w => e x * w) h_sig_id.1.symm
          _ = (e x * σ.σ x y) * e x := (mul_assoc _ _ _).symm
          _ = e x * σ.σ x y * e x := by simp only [mul_assoc]
          _ = e x := h_ese_eq_e
      exact ⟨e x, he_D, he_idem x, h_final_sigma⟩
    obtain ⟨e_id, _, he_idem_final, he_eq⟩ := h_sigma_eq_idem
    rw [he_eq]
    exact he_idem_final

end RegularDClassCase
