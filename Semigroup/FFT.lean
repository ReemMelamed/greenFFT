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

structure SimonContext (S α : Type*) [Semigroup S] [Fintype S] [LinearOrder α] where
  σ : MultiplicativeLabeling S α
  D : Set S
  x₀ : S
  hx₀ : D = IsGreenD.eqvClass x₀
  hReg : IsRegularDClass D
  h_range : ∀ x y, x < y → σ.σ x y ∈ D

omit [Fintype S] [Fintype α] [Nonempty α] in
def is_max (x : α) : Prop := ∀ y, y ≤ x

omit [Fintype S] [Fintype α] [Nonempty α] in
def is_min (x : α) : Prop := ∀ y, x ≤ y

omit [Fintype S] [Fintype α] [Nonempty α] in
lemma exists_lt_of_not_min {x : α} (h : ¬ is_min x) : ∃ y, y < x := by
  by_contra hc; push_neg at hc; exact h hc

omit [Fintype S] [Fintype α] [Nonempty α] in
lemma exists_gt_of_not_max {x : α} (h : ¬ is_max x) : ∃ y, x < y := by
  by_contra hc; push_neg at hc; exact h hc

omit [Fintype S] [Fintype α] [Nonempty α] in
open Classical in
noncomputable def get_lt (x : α) (h : ¬ is_min x) : α :=
  Classical.choose (exists_lt_of_not_min h)

omit [Fintype S] [Fintype α] [Nonempty α] in
lemma get_lt_prop (x : α) (h : ¬ is_min x) : get_lt x h < x :=
  Classical.choose_spec (exists_lt_of_not_min h)

omit [Fintype S] [Fintype α] [Nonempty α] in
open Classical in
noncomputable def get_gt (x : α) (h : ¬ is_max x) : α :=
  Classical.choose (exists_gt_of_not_max h)

omit [Fintype S] [Fintype α] [Nonempty α] in
lemma get_gt_prop (x : α) (h : ¬ is_max x) : x < get_gt x h :=
  Classical.choose_spec (exists_gt_of_not_max h)

omit [Fintype α] [Nonempty α] in
open Classical in
noncomputable def L_of (ctx : SimonContext S α) (x : α) : Set S :=
  if h_min : is_min x then
    if h_max : is_max x then
      IsGreenL.eqvClass ctx.x₀
    else
      have ha_D : ctx.σ.σ x (get_gt x h_max) ∈ ctx.D := ctx.h_range x _ (get_gt_prop x h_max)
      IsGreenL.eqvClass (Classical.choose (exists_idempotent_in_greenR_of_regular (ctx.hReg _ ha_D)))
  else
    IsGreenL.eqvClass (ctx.σ.σ (get_lt x h_min) x)

omit [Fintype α] [Nonempty α] in
open Classical in
noncomputable def R_of (ctx : SimonContext S α) (x : α) : Set S :=
  if h_max : is_max x then
    if h_min : is_min x then
      have ha_D : ctx.x₀ ∈ ctx.D := by rw [ctx.hx₀]; exact IsGreenD.refl ctx.x₀
      IsGreenR.eqvClass (Classical.choose (exists_idempotent_in_greenL_of_regular (ctx.hReg _ ha_D)))
    else
      have ha_D : ctx.σ.σ (get_lt x h_min) x ∈ ctx.D := ctx.h_range _ x (get_lt_prop x h_min)
      IsGreenR.eqvClass (Classical.choose (exists_idempotent_in_greenL_of_regular (ctx.hReg _ ha_D)))
  else
    IsGreenR.eqvClass (ctx.σ.σ x (get_gt x h_max))

omit [Fintype α] [Nonempty α] in
noncomputable def H_of (ctx : SimonContext S α) (x : α) : Set S :=
  L_of ctx x ∩ R_of ctx x

omit [Fintype α] [Nonempty α] in
lemma L_of_well_defined (ctx : SimonContext S α) (x y1 y2 : α) (_h_not_min : ¬ is_min x) (hy1 : y1 < x) (hy2 : y2 < x) :
    IsGreenL.eqvClass (ctx.σ.σ y1 x) = IsGreenL.eqvClass (ctx.σ.σ y2 x) := by
  wlog h_le : y1 ≤ y2 generalizing y1 y2 hy1 hy2
  · exact (this y2 y1 hy2 hy1 (le_of_lt (not_le.mp h_le))).symm
  · rcases h_le.eq_or_lt with rfl | h_lt
    · rfl
    · have h_prod : ctx.σ.σ y1 x = ctx.σ.σ y1 y2 * ctx.σ.σ y2 x := (ctx.σ.prop y1 y2 x h_lt hy2).symm
      have h12 : ctx.σ.σ y1 y2 ∈ ctx.D := ctx.h_range y1 y2 h_lt
      have h2x : ctx.σ.σ y2 x ∈ ctx.D := ctx.h_range y2 x hy2
      have h1x : ctx.σ.σ y1 x ∈ ctx.D := ctx.h_range y1 x hy1
      have hL_raw := (mul_mem_isGreenD_eqvClass_properties ⟨ctx.x₀, ctx.hx₀⟩ (ctx.σ.σ y1 y2) (ctx.σ.σ y2 x) h12 h2x (h_prod ▸ h1x)).1.2
      have hL : IsGreenL (ctx.σ.σ y2 x) (ctx.σ.σ y1 x) := h_prod ▸ hL_raw
      ext z
      constructor
      · intro hz; exact IsGreenL.trans hz (IsGreenL.symm hL)
      · intro hz; exact IsGreenL.trans hz hL

omit [Fintype α] [Nonempty α] in
lemma R_of_well_defined (ctx : SimonContext S α) (x y1 y2 : α) (_h_not_max : ¬ is_max x) (hy1 : x < y1) (hy2 : x < y2) :
    IsGreenR.eqvClass (ctx.σ.σ x y1) = IsGreenR.eqvClass (ctx.σ.σ x y2) := by
  wlog h_le : y1 ≤ y2 generalizing y1 y2 hy1 hy2
  · exact (this y2 y1 hy2 hy1 (le_of_lt (not_le.mp h_le))).symm
  · rcases h_le.eq_or_lt with rfl | h_lt
    · rfl
    · have h_prod : ctx.σ.σ x y1 * ctx.σ.σ y1 y2 = ctx.σ.σ x y2 := ctx.σ.prop x y1 y2 hy1 h_lt
      have hx1 : ctx.σ.σ x y1 ∈ ctx.D := ctx.h_range x y1 hy1
      have h12 : ctx.σ.σ y1 y2 ∈ ctx.D := ctx.h_range y1 y2 h_lt
      have hx2 : ctx.σ.σ x y2 ∈ ctx.D := ctx.h_range x y2 hy2
      have hR_raw := (mul_mem_isGreenD_eqvClass_properties ⟨ctx.x₀, ctx.hx₀⟩ (ctx.σ.σ x y1) (ctx.σ.σ y1 y2) hx1 h12 (h_prod.symm ▸ hx2)).1.1
      have hR : IsGreenR (ctx.σ.σ x y1) (ctx.σ.σ x y2) := h_prod ▸ hR_raw
      ext z
      constructor
      · intro hz; exact IsGreenR.trans hz hR
      · intro hz; exact IsGreenR.trans hz (IsGreenR.symm hR)

omit [Fintype α] [Nonempty α] in
lemma H_of_has_idempotent (ctx : SimonContext S α) (x : α) :
    ∃ e_id : S, e_id ∈ H_of ctx x ∧ e_id * e_id = e_id := by
  dsimp [H_of]
  by_cases h_min : is_min x
  · by_cases h_max : is_max x
    · have ha_D : ctx.x₀ ∈ ctx.D := by rw [ctx.hx₀]; exact IsGreenD.refl ctx.x₀
      let ex : S := Classical.choose (exists_idempotent_in_greenL_of_regular (ctx.hReg _ ha_D))
      have he_prop := Classical.choose_spec (exists_idempotent_in_greenL_of_regular (ctx.hReg _ ha_D))
      use ex
      refine ⟨⟨?_, ?_⟩, he_prop.right⟩
      · simp only [L_of, h_min, h_max, dite_true]
        exact he_prop.left
      · simp only [R_of, h_max, h_min, dite_true]
        exact IsGreenR.refl ex
    · have ha_D : ctx.σ.σ x (get_gt x h_max) ∈ ctx.D := ctx.h_range x _ (get_gt_prop x h_max)
      let ex : S := Classical.choose (exists_idempotent_in_greenR_of_regular (ctx.hReg _ ha_D))
      have he_prop := Classical.choose_spec (exists_idempotent_in_greenR_of_regular (ctx.hReg _ ha_D))
      use ex
      refine ⟨⟨?_, ?_⟩, he_prop.right⟩
      · simp only [L_of, h_min, h_max, dite_true, dite_false]
        exact IsGreenL.refl ex
      · simp only [R_of, h_max, dite_false]
        exact he_prop.left
  · by_cases h_max : is_max x
    · have ha_D : ctx.σ.σ (get_lt x h_min) x ∈ ctx.D := ctx.h_range _ x (get_lt_prop x h_min)
      let ex : S := Classical.choose (exists_idempotent_in_greenL_of_regular (ctx.hReg _ ha_D))
      have he_prop := Classical.choose_spec (exists_idempotent_in_greenL_of_regular (ctx.hReg _ ha_D))
      use ex
      refine ⟨⟨?_, ?_⟩, he_prop.right⟩
      · simp only [L_of, h_min, dite_false]
        exact he_prop.left
      · simp only [R_of, h_max, h_min, dite_true, dite_false]
        exact IsGreenR.refl ex
    · have ha : ctx.σ.σ (get_lt x h_min) x ∈ ctx.D := ctx.h_range _ _ (get_lt_prop x h_min)
      have hb : ctx.σ.σ x (get_gt x h_max) ∈ ctx.D := ctx.h_range _ _ (get_gt_prop x h_max)
      have hab : ctx.σ.σ (get_lt x h_min) x * ctx.σ.σ x (get_gt x h_max) ∈ ctx.D := by
        rw [ctx.σ.prop _ _ _ (get_lt_prop x h_min) (get_gt_prop x h_max)]
        exact ctx.h_range _ _ (lt_trans (get_lt_prop x h_min) (get_gt_prop x h_max))
      obtain ⟨_, ⟨ex, _, he_idem, hLe, hRe⟩⟩ :=
        mul_mem_isGreenD_eqvClass_properties ⟨ctx.x₀, ctx.hx₀⟩ _ _ ha hb hab
      use ex
      refine ⟨⟨?_, ?_⟩, he_idem⟩
      · simp only [L_of, h_min, dite_false]
        exact IsGreenL.symm hLe
      · simp only [R_of, h_max, dite_false]
        exact IsGreenR.symm hRe

omit [Fintype α] [Nonempty α] in
open Classical in
noncomputable def e_id (ctx : SimonContext S α) (x : α) : S :=
  Classical.choose (H_of_has_idempotent ctx x)

omit [Fintype α] [Nonempty α] in
lemma e_id_mem (ctx : SimonContext S α) (x : α) : e_id ctx x ∈ H_of ctx x :=
  (Classical.choose_spec (H_of_has_idempotent ctx x)).1

omit [Fintype α] [Nonempty α] in
lemma e_id_idem (ctx : SimonContext S α) (x : α) : e_id ctx x * e_id ctx x = e_id ctx x :=
  (Classical.choose_spec (H_of_has_idempotent ctx x)).2

omit [Fintype α] [Nonempty α] in
lemma H_of_eq_class (ctx : SimonContext S α) (z : α) : H_of ctx z = IsGreenH.eqvClass (e_id ctx z) := by
  ext w
  constructor
  · rintro ⟨hwL, hwR⟩
    have h1 : e_id ctx z ∈ L_of ctx z := (e_id_mem ctx z).1
    have h2 : e_id ctx z ∈ R_of ctx z := (e_id_mem ctx z).2
    have he_L_rel : IsGreenL (e_id ctx z) w := by
      dsimp only [L_of] at h1 hwL
      split_ifs at h1 hwL <;> exact IsGreenL.trans h1 (IsGreenL.symm hwL)
    have he_R_rel : IsGreenR (e_id ctx z) w := by
      dsimp only [R_of] at h2 hwR
      split_ifs at h2 hwR <;> exact IsGreenR.trans h2 (IsGreenR.symm hwR)
    exact ⟨IsGreenL.symm he_L_rel, IsGreenR.symm he_R_rel⟩
  · rintro ⟨hwL, hwR⟩
    have h1 : e_id ctx z ∈ L_of ctx z := (e_id_mem ctx z).1
    have h2 : e_id ctx z ∈ R_of ctx z := (e_id_mem ctx z).2
    have hw_L_mem : w ∈ L_of ctx z := by
      dsimp only [L_of] at h1 ⊢
      split_ifs at h1 ⊢ <;> exact IsGreenL.trans hwL h1
    have hw_R_mem : w ∈ R_of ctx z := by
      dsimp only [R_of] at h2 ⊢
      split_ifs at h2 ⊢ <;> exact IsGreenR.trans hwR h2
    exact ⟨hw_L_mem, hw_R_mem⟩

omit [Fintype α] [Nonempty α] in
lemma sigma_props (ctx : SimonContext S α) (z mz : α) (h_mz : mz < z) (hm_H : H_of ctx mz = H_of ctx z) :
    e_id ctx z * ctx.σ.σ mz z * e_id ctx z = ctx.σ.σ mz z ∧ IsGreenH (ctx.σ.σ mz z) (e_id ctx z) := by
  have he_z_idem : e_id ctx z * e_id ctx z = e_id ctx z := e_id_idem ctx z
  have h_not_min_z : ¬ is_min z := fun h => lt_irrefl mz (lt_of_lt_of_le h_mz (h mz))
  have h_L_mz : L_of ctx z = IsGreenL.eqvClass (ctx.σ.σ mz z) := by
    dsimp only [L_of]
    rw [dif_neg h_not_min_z]
    exact L_of_well_defined ctx z (get_lt z h_not_min_z) mz h_not_min_z (get_lt_prop z h_not_min_z) h_mz
  have he_L_mz_z : IsGreenL (e_id ctx z) (ctx.σ.σ mz z) := by
    have h1 : e_id ctx z ∈ L_of ctx z := (e_id_mem ctx z).1
    rwa [h_L_mz] at h1
  have h_not_max_m : ¬ is_max mz := fun h => lt_irrefl z (lt_of_le_of_lt (h z) h_mz)
  have h_R_mz : R_of ctx mz = IsGreenR.eqvClass (ctx.σ.σ mz z) := by
    dsimp only [R_of]
    rw [dif_neg h_not_max_m]
    exact R_of_well_defined ctx mz (get_gt mz h_not_max_m) z h_not_max_m (get_gt_prop mz h_not_max_m) h_mz
  have he_R_mz_z : IsGreenR (e_id ctx z) (ctx.σ.σ mz z) := by
    have hz_in_H : e_id ctx z ∈ H_of ctx mz := hm_H ▸ e_id_mem ctx z
    have h1 : e_id ctx z ∈ R_of ctx mz := hz_in_H.2
    rwa [h_R_mz] at h1
  have he_H_mz_z : IsGreenH (e_id ctx z) (ctx.σ.σ mz z) := ⟨he_L_mz_z, he_R_mz_z⟩
  have h_sig_H_e : IsGreenH (ctx.σ.σ mz z) (e_id ctx z) := IsGreenH.symm he_H_mz_z
  have hid := mul_eq_self_of_isGreenH_idempotent h_sig_H_e he_z_idem
  have h_simp : e_id ctx z * ctx.σ.σ mz z * e_id ctx z = ctx.σ.σ mz z := by
    calc e_id ctx z * ctx.σ.σ mz z * e_id ctx z = (e_id ctx z * ctx.σ.σ mz z) * e_id ctx z := by simp only [mul_assoc]
      _ = ctx.σ.σ mz z * e_id ctx z := by rw [hid.2]
      _ = ctx.σ.σ mz z := hid.1
  exact ⟨h_simp, h_sig_H_e⟩

abbrev G_D_type (D : Set S) :=
  { y : S // y ∈ D ∧ ∃ e ∈ D, e * e = e ∧ IsGreenH y e }

open Classical in
noncomputable def f_coloring (ctx : SimonContext S α) (x : α) : G_D_type ctx.D :=
  let m_class := Finset.univ.filter (fun y => H_of ctx y = H_of ctx x)
  have hm_nonempty : m_class.Nonempty := ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, rfl⟩⟩
  let m := Finset.min' m_class hm_nonempty
  if h_mx : m < x then
      let val := e_id ctx x * ctx.σ.σ m x * e_id ctx x
      have h_val_in : val ∈ ctx.D ∧ ∃ e' ∈ ctx.D, e' * e' = e' ∧ IsGreenH val e' := by
        have he_idem_x : e_id ctx x * e_id ctx x = e_id ctx x := e_id_idem ctx x
        have hm_in := Finset.min'_mem m_class hm_nonempty
        have hm_H : H_of ctx m = H_of ctx x := (Finset.mem_filter.mp hm_in).2
        have h_not_min_x : ¬ is_min x := fun h => lt_irrefl m (lt_of_lt_of_le h_mx (h m))
        have h_L_mx : L_of ctx x = IsGreenL.eqvClass (ctx.σ.σ m x) := by
          dsimp only [L_of]
          rw [dif_neg h_not_min_x]
          exact L_of_well_defined ctx x (get_lt x h_not_min_x) m h_not_min_x (get_lt_prop x h_not_min_x) h_mx
        have he_L_sig : IsGreenL (e_id ctx x) (ctx.σ.σ m x) := by
          have h1 : e_id ctx x ∈ L_of ctx x := (e_id_mem ctx x).1
          rwa [h_L_mx] at h1
        have h_not_max_m : ¬ is_max m := fun h => lt_irrefl x (lt_of_le_of_lt (h x) h_mx)
        have h_R_m : R_of ctx m = IsGreenR.eqvClass (ctx.σ.σ m x) := by
          dsimp only [R_of]
          rw [dif_neg h_not_max_m]
          exact R_of_well_defined ctx m (get_gt m h_not_max_m) x h_not_max_m (get_gt_prop m h_not_max_m) h_mx
        have he_R_sig : IsGreenR (e_id ctx x) (ctx.σ.σ m x) := by
          have hx_in_H : e_id ctx x ∈ H_of ctx m := hm_H ▸ e_id_mem ctx x
          have h1 : e_id ctx x ∈ R_of ctx m := hx_in_H.2
          rwa [h_R_m] at h1
        have he_H_sig : IsGreenH (e_id ctx x) (ctx.σ.σ m x) := ⟨he_L_sig, he_R_sig⟩
        have h_sig_H_e : IsGreenH (ctx.σ.σ m x) (e_id ctx x) := IsGreenH.symm he_H_sig
        have h_class_eq : ∃ a, IsGreenH.eqvClass (e_id ctx x) = IsGreenH.eqvClass a := ⟨e_id ctx x, rfl⟩
        have h_group_or := is_group_isGreenH_eqvClass_iff_idempotent (IsGreenH.eqvClass (e_id ctx x)) h_class_eq
        have h_group : ∀ u v, u ∈ IsGreenH.eqvClass (e_id ctx x) → v ∈ IsGreenH.eqvClass (e_id ctx x) → u * v ∈ IsGreenH.eqvClass (e_id ctx x) := by
          rcases h_group_or with h_empty | ⟨e', he'H, he'idem, h_mul⟩
          · have h_ee_not := h_empty (e_id ctx x) (e_id ctx x) (IsGreenH.refl (e_id ctx x)) (IsGreenH.refl (e_id ctx x))
            rw [he_idem_x] at h_ee_not
            exact False.elim (h_ee_not (IsGreenH.refl (e_id ctx x)))
          · exact h_mul
        have h_sig_He : ctx.σ.σ m x ∈ IsGreenH.eqvClass (e_id ctx x) := h_sig_H_e
        have he_He : e_id ctx x ∈ IsGreenH.eqvClass (e_id ctx x) := IsGreenH.refl (e_id ctx x)
        have h_val_He : val ∈ IsGreenH.eqvClass (e_id ctx x) := by
          dsimp only [val]
          have h1 := h_group (e_id ctx x) (ctx.σ.σ m x) he_He h_sig_He
          exact h_group (e_id ctx x * ctx.σ.σ m x) (e_id ctx x) h1 he_He
        have h_val_H_e : IsGreenH val (e_id ctx x) := h_val_He
        have h_sig_D : ctx.σ.σ m x ∈ ctx.D := ctx.h_range m x h_mx
        have he_D_sig : IsGreenD (e_id ctx x) (ctx.σ.σ m x) := ⟨e_id ctx x, IsGreenL.refl (e_id ctx x), he_H_sig.right⟩
        have he_D : e_id ctx x ∈ ctx.D := by
          rw [ctx.hx₀] at h_sig_D ⊢
          exact IsGreenD.trans he_D_sig h_sig_D
        have hval_D_e : IsGreenD val (e_id ctx x) := ⟨val, IsGreenL.refl val, h_val_H_e.right⟩
        have h_val_D : val ∈ ctx.D := by
          rw [ctx.hx₀] at he_D ⊢
          exact IsGreenD.trans hval_D_e he_D
        exact ⟨h_val_D, e_id ctx x, he_D, he_idem_x, h_val_H_e⟩
      ⟨val, h_val_in⟩
  else
      have h_e_in : e_id ctx x ∈ ctx.D ∧ ∃ e' ∈ ctx.D, e' * e' = e' ∧ IsGreenH (e_id ctx x) e' := by
        have he_idem_x := e_id_idem ctx x
        have he_D : e_id ctx x ∈ ctx.D := by
          have he_L : e_id ctx x ∈ L_of ctx x := (e_id_mem ctx x).1
          by_cases h_min : is_min x
          · by_cases h_max : is_max x
            · dsimp only [L_of] at he_L
              rw [dif_pos h_min, dif_pos h_max] at he_L
              rw [ctx.hx₀]
              exact ⟨ctx.x₀, he_L, IsGreenR.refl ctx.x₀⟩
            · let y' := get_gt x h_max
              have ha_D : ctx.σ.σ x y' ∈ ctx.D := ctx.h_range x y' (get_gt_prop x h_max)
              dsimp only [L_of] at he_L
              rw [dif_pos h_min, dif_neg h_max] at he_L
              let e_R : S := Classical.choose (exists_idempotent_in_greenR_of_regular (ctx.hReg _ ha_D))
              have he_R_prop := Classical.choose_spec (exists_idempotent_in_greenR_of_regular (ctx.hReg _ ha_D))
              rw [ctx.hx₀] at ha_D ⊢
              have hD_e_sig : IsGreenD (e_id ctx x) (ctx.σ.σ x y') := ⟨e_R, he_L, he_R_prop.left⟩
              exact IsGreenD.trans hD_e_sig ha_D
          · let y' := get_lt x h_min
            dsimp only [L_of] at he_L
            rw [dif_neg h_min] at he_L
            have ha_D : ctx.σ.σ y' x ∈ ctx.D := ctx.h_range y' x (get_lt_prop x h_min)
            rw [ctx.hx₀] at ha_D ⊢
            have hD_e_sig : IsGreenD (e_id ctx x) (ctx.σ.σ y' x) := ⟨ctx.σ.σ y' x, he_L, IsGreenR.refl _⟩
            exact IsGreenD.trans hD_e_sig ha_D
        exact ⟨he_D, e_id ctx x, he_D, he_idem_x, IsGreenH.refl (e_id ctx x)⟩
      ⟨e_id ctx x, h_e_in⟩

omit [Nonempty α] in
lemma f_coloring_H (ctx : SimonContext S α) (z : α) : IsGreenH (f_coloring ctx z).val (e_id ctx z) := by
  let m_class := Finset.univ.filter (fun w => H_of ctx w = H_of ctx z)
  have hm_nonempty : m_class.Nonempty := ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ z, rfl⟩⟩
  let mz := Finset.min' m_class hm_nonempty
  have hm_in := Finset.min'_mem m_class hm_nonempty
  have hm_H : H_of ctx mz = H_of ctx z := (Finset.mem_filter.mp hm_in).2
  have h_val : (f_coloring ctx z).val = if h_lt : mz < z then e_id ctx z * ctx.σ.σ mz z * e_id ctx z else e_id ctx z := by
    dsimp only [f_coloring]; split_ifs <;> rfl
  rw [h_val]
  split_ifs with h_mz
  · have h_props := sigma_props ctx z mz h_mz hm_H
    rw [h_props.1]
    exact h_props.2
  · exact IsGreenH.refl (e_id ctx z)

open Classical in
lemma simon_regular_d_case
    (σ : MultiplicativeLabeling S α)
    (D : Set S)
    (hD : ∃ x, D = IsGreenD.eqvClass x)
    (hReg : IsRegularDClass D)
    (h_range : ∀ x y, x < y → σ.σ x y ∈ D)
    (h_ne : Nonempty (Fin (nD D)) := Fin.pos_iff_nonempty.mp (nD_pos D hD)) :
    ∃ (s : Split α (nD D)), IsNormalized s ∧ IsRamsey σ s := by
  obtain ⟨x₀, hx₀⟩ := hD
  let ctx : SimonContext S α := {
    σ := σ,
    D := D,
    x₀ := x₀,
    hx₀ := hx₀,
    hReg := hReg,
    h_range := h_range
  }
  have h_card_G_D : Fintype.card (G_D_type D) = nD D := by
    dsimp [nD]; rw [if_pos hReg]; exact Fintype.card_subtype _
  have h_card_pos : 0 < Fintype.card (G_D_type D) := by
    rw [h_card_G_D]; exact Fin.pos_iff_nonempty.mpr (Fin.pos_iff_nonempty.mp (nD_pos D ⟨x₀, hx₀⟩))
  let max_rank : Fin (nD D) := Fin.cast h_card_G_D (Fin.cast (Nat.sub_add_cancel h_card_pos) (Fin.last (Fintype.card (G_D_type D) - 1)))
  let equiv_G_D_Fin : G_D_type D ≃ Fin (nD D) := (Fintype.equivFin _).trans (Equiv.cast (congrArg Fin h_card_G_D))
  let alpha_min : α := Finset.min' Finset.univ Finset.univ_nonempty
  let index_map := equiv_G_D_Fin.trans (Equiv.swap (equiv_G_D_Fin (f_coloring ctx alpha_min)) max_rank)
  let s : Split α (nD D) := fun y => index_map (f_coloring ctx y)
  use s
  constructor
  · change s alpha_min = Finset.max' Finset.univ Finset.univ_nonempty
    have h_min_eval : s alpha_min = max_rank := by
      dsimp only [s, index_map]; rw [Equiv.trans_apply, Equiv.swap_apply_left]
    rw [h_min_eval]; symm; rw [Finset.max'_eq_iff]
    constructor
    · exact Finset.mem_univ _
    · intro y _
      apply Fin.le_iff_val_le_val.mpr
      have h_max_val : (max_rank : ℕ) = nD D - 1 := by simp [max_rank]; rw [h_card_G_D]
      rw [h_max_val]
      exact Nat.le_pred_of_lt y.is_lt
  · intros x y hlt hsr
    unfold SplitRelation at hsr
    have h_f_eq : f_coloring ctx x = f_coloring ctx y := Equiv.injective index_map hsr.left
    have h_val_eq : (f_coloring ctx x).val = (f_coloring ctx y).val := congrArg Subtype.val h_f_eq
    have h_fz_H_e := f_coloring_H ctx x
    have h_fy_H_ey := f_coloring_H ctx y
    have he_H_ey : IsGreenH (e_id ctx x) (e_id ctx y) := by
      have h1 : IsGreenH (e_id ctx x) (f_coloring ctx x).val := IsGreenH.symm h_fz_H_e
      exact IsGreenH.trans h1 (h_val_eq ▸ h_fy_H_ey)
    have he_eq_ey : e_id ctx x = e_id ctx y := eq_of_isGreenH_of_idempotent he_H_ey (e_id_idem ctx x) (e_id_idem ctx y)
    let m_class_x := Finset.univ.filter (fun z => H_of ctx z = H_of ctx x)
    let m_class_y := Finset.univ.filter (fun z => H_of ctx z = H_of ctx y)
    have hm_nonempty_x : m_class_x.Nonempty := ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, rfl⟩⟩
    have hm_nonempty_y : m_class_y.Nonempty := ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ y, rfl⟩⟩
    let mx := Finset.min' m_class_x hm_nonempty_x
    let my := Finset.min' m_class_y hm_nonempty_y
    have h_same_H : H_of ctx x = H_of ctx y := by rw [H_of_eq_class ctx x, H_of_eq_class ctx y, he_eq_ey]
    have h_mx_eq_my : mx = my := by
      have h_class_eq : m_class_x = m_class_y := by
        ext z
        simp only [m_class_x, m_class_y, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => h.trans h_same_H, fun h => h.trans h_same_H.symm⟩
      apply le_antisymm
      · have h_my_in_x : my ∈ m_class_x := by rw [h_class_eq]; exact Finset.min'_mem m_class_y hm_nonempty_y
        have hmy_in_mx : my ∈ m_class_x := h_my_in_x
        exact Finset.min'_le m_class_x my hmy_in_mx
      · have h_mx_in_y : mx ∈ m_class_y := by rw [← h_class_eq]; exact Finset.min'_mem m_class_x hm_nonempty_x
        have hmx_in_my : mx ∈ m_class_y := h_mx_in_y
        exact Finset.min'_le m_class_y mx hmx_in_my
    have h_ese_eq_e : e_id ctx x * σ.σ x y * e_id ctx x = e_id ctx x := by
      by_cases h_mx : mx < x
      · have h_mem_x := Finset.min'_mem m_class_x hm_nonempty_x
        have hm_H : H_of ctx mx = H_of ctx x := (Finset.mem_filter.mp h_mem_x).2
        have h_props_x := sigma_props ctx x mx h_mx hm_H
        have h_val_x : (f_coloring ctx x).val = if h_lt : mx < x then e_id ctx x * σ.σ mx x * e_id ctx x else e_id ctx x := by
          dsimp only [f_coloring]; split_ifs <;> rfl
        have h_fx : (f_coloring ctx x).val = σ.σ mx x := by rw [h_val_x, dif_pos h_mx]; exact h_props_x.1
        have h_my : my < y := by rw [← h_mx_eq_my]; exact lt_trans h_mx hlt
        have h_mem_y := Finset.min'_mem m_class_y hm_nonempty_y
        have hm_Hy : H_of ctx my = H_of ctx y := (Finset.mem_filter.mp h_mem_y).2
        have h_props_y := sigma_props ctx y my h_my hm_Hy
        have h_val_y : (f_coloring ctx y).val = if h_lt : my < y then e_id ctx y * σ.σ my y * e_id ctx y else e_id ctx y := by
          dsimp only [f_coloring]; split_ifs <;> rfl
        have h_fy : (f_coloring ctx y).val = σ.σ my y := by rw [h_val_y, dif_pos h_my]; exact h_props_y.1
        have hid_mx_mul := mul_eq_self_of_isGreenH_idempotent h_props_x.2 (e_id_idem ctx x)
        have hid_my_mul := mul_eq_self_of_isGreenH_idempotent h_props_y.2 (e_id_idem ctx y)
        have h_v_eq : σ.σ mx x * σ.σ x y * e_id ctx x = σ.σ mx x := by
          calc σ.σ mx x * σ.σ x y * e_id ctx x = (e_id ctx x * σ.σ mx x) * σ.σ x y * e_id ctx x := congrArg (fun w => w * σ.σ x y * e_id ctx x) hid_mx_mul.2.symm
            _ = e_id ctx x * (σ.σ mx x * σ.σ x y) * e_id ctx x := by simp only [mul_assoc]
            _ = e_id ctx x * σ.σ mx y * e_id ctx x := by rw [← σ.prop mx x y h_mx hlt]
            _ = e_id ctx y * σ.σ my y * e_id ctx y := by rw [he_eq_ey, h_mx_eq_my]
            _ = (e_id ctx y * σ.σ my y) * e_id ctx y := by simp only [mul_assoc]
            _ = σ.σ my y * e_id ctx y := by rw [hid_my_mul.2]
            _ = σ.σ my y := hid_my_mul.1
            _ = (f_coloring ctx y).val := h_fy.symm
            _ = (f_coloring ctx x).val := h_val_eq.symm
            _ = σ.σ mx x := h_fx
        have he_L_sig : IsGreenL (e_id ctx x) (σ.σ mx x) := IsGreenL.symm h_props_x.2.left
        rcases he_L_sig.left with heq | ⟨u, hu⟩
        · calc e_id ctx x * σ.σ x y * e_id ctx x = σ.σ mx x * σ.σ x y * e_id ctx x := by rw [heq]
            _ = σ.σ mx x := h_v_eq
            _ = e_id ctx x := heq.symm
        · calc e_id ctx x * σ.σ x y * e_id ctx x = (u * σ.σ mx x) * σ.σ x y * e_id ctx x := by rw [hu]
            _ = u * (σ.σ mx x * σ.σ x y * e_id ctx x) := by simp only [mul_assoc]
            _ = u * σ.σ mx x := by rw [h_v_eq]
            _ = e_id ctx x := hu.symm
      · have h_x_le_mx : x ≤ mx := not_lt.mp h_mx
        have hx_in_mx : x ∈ m_class_x := Finset.mem_filter.mpr ⟨Finset.mem_univ x, rfl⟩
        have h_mx_le_x : mx ≤ x := Finset.min'_le m_class_x x hx_in_mx
        have h_mx_eq : mx = x := le_antisymm h_mx_le_x h_x_le_mx
        have h_val_x : (f_coloring ctx x).val = if h_lt : mx < x then e_id ctx x * σ.σ mx x * e_id ctx x else e_id ctx x := by
          dsimp only [f_coloring]; split_ifs <;> rfl
        have h_fx : (f_coloring ctx x).val = e_id ctx x := by rw [h_val_x, dif_neg h_mx]
        have h_my : my < y := by rw [← h_mx_eq_my, h_mx_eq]; exact hlt
        have h_mem_y := Finset.min'_mem m_class_y hm_nonempty_y
        have hm_Hy : H_of ctx my = H_of ctx y := (Finset.mem_filter.mp h_mem_y).2
        have h_props_y := sigma_props ctx y my h_my hm_Hy
        have h_val_y : (f_coloring ctx y).val = if h_lt : my < y then e_id ctx y * σ.σ my y * e_id ctx y else e_id ctx y := by
          dsimp only [f_coloring]; split_ifs <;> rfl
        have h_fy : (f_coloring ctx y).val = σ.σ my y := by rw [h_val_y, dif_pos h_my]; exact h_props_y.1
        have hid_my_mul := mul_eq_self_of_isGreenH_idempotent h_props_y.2 (e_id_idem ctx y)
        calc e_id ctx x * σ.σ x y * e_id ctx x = e_id ctx y * σ.σ my y * e_id ctx y := by rw [← he_eq_ey, ← h_mx_eq_my, h_mx_eq]
          _ = (e_id ctx y * σ.σ my y) * e_id ctx y := by simp only [mul_assoc]
          _ = σ.σ my y * e_id ctx y := by rw [hid_my_mul.2]
          _ = σ.σ my y := hid_my_mul.1
          _ = (f_coloring ctx y).val := h_fy.symm
          _ = (f_coloring ctx x).val := h_val_eq.symm
          _ = e_id ctx x := h_fx
    have h_sig_H : IsGreenH (σ.σ x y) (e_id ctx x) := by
      have h_not_min_y : ¬ is_min y := fun h => lt_irrefl x (lt_of_lt_of_le hlt (h x))
      have h_L_y : L_of ctx y = IsGreenL.eqvClass (σ.σ x y) := by
        dsimp only [L_of]; rw [dif_neg h_not_min_y]
        exact L_of_well_defined ctx y (get_lt y h_not_min_y) x h_not_min_y (get_lt_prop y h_not_min_y) hlt
      have hex_in_Hy : e_id ctx x ∈ H_of ctx y := h_same_H ▸ e_id_mem ctx x
      have he_L : e_id ctx x ∈ L_of ctx y := hex_in_Hy.1
      have he_L_mem : IsGreenL (e_id ctx x) (σ.σ x y) := by rwa [h_L_y] at he_L
      have h_not_max_x : ¬ is_max x := fun h => lt_irrefl y (lt_of_le_of_lt (h y) hlt)
      have h_R_x : R_of ctx x = IsGreenR.eqvClass (σ.σ x y) := by
        dsimp only [R_of]; rw [dif_neg h_not_max_x]
        exact R_of_well_defined ctx x (get_gt x h_not_max_x) y h_not_max_x (get_gt_prop x h_not_max_x) hlt
      have he_R : e_id ctx x ∈ R_of ctx x := (e_id_mem ctx x).2
      have he_R_mem : IsGreenR (e_id ctx x) (σ.σ x y) := by rwa [h_R_x] at he_R
      exact IsGreenH.symm ⟨he_L_mem, he_R_mem⟩
    have h_final_sigma : σ.σ x y = e_id ctx x := by
      have h_sig_id := mul_eq_self_of_isGreenH_idempotent h_sig_H (e_id_idem ctx x)
      calc σ.σ x y = e_id ctx x * σ.σ x y := h_sig_id.2.symm
        _ = e_id ctx x * (σ.σ x y * e_id ctx x) := congrArg (fun w => e_id ctx x * w) h_sig_id.1.symm
        _ = (e_id ctx x * σ.σ x y) * e_id ctx x := (mul_assoc _ _ _).symm
        _ = e_id ctx x * σ.σ x y * e_id ctx x := by simp only [mul_assoc]
        _ = e_id ctx x := h_ese_eq_e
    rw [h_final_sigma]
    exact e_id_idem ctx x

end RegularDClassCase
