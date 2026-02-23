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

  let is_max (x : α) : Prop := ∀ y, y ≤ x
  let is_min (x : α) : Prop := ∀ y, x ≤ y

  let L_of (x : α) : Set S :=
    if h_min : is_min x then
      let x₀ := Classical.choose hD
      greenLClass x₀
    else
      have h_exists : ∃ y, y < x := by
        contrapose! h_min
        exact h_min
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
        have hL_raw := (mul_mem_green_d_properties hD (σ.σ y1 y2) (σ.σ y2 x) h12 h2x (h_prod ▸ h1x)).1.2
        have hL : GreenL (σ.σ y2 x) (σ.σ y1 x) := h_prod ▸ hL_raw
        ext z
        constructor
        · intro hz; exact green_l_trans hz (green_l_symm hL)
        · intro hz; exact green_l_trans hz hL

  let R_of (x : α) : Set S :=
    if h_max : is_max x then
      let min_α := Finset.min' Finset.univ Finset.univ_nonempty
      let H_min := L_of min_α
      have h_reg_L : ∃ e ∈ H_min, e * e = e := by
        sorry
      let e := Classical.choose h_reg_L
      greenRClass e
    else
      have h_exists : ∃ y, x < y := by
        contrapose! h_max
        exact h_max
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
        have hR_raw := (mul_mem_green_d_properties hD (σ.σ x y1) (σ.σ y1 y2) hx1 h12 (h_prod.symm ▸ hx2)).1.1
        have hR : GreenR (σ.σ x y1) (σ.σ x y2) := h_prod ▸ hR_raw
        ext z
        constructor
        · intro hz; exact green_r_trans hz hR
        · intro hz; exact green_r_trans hz (green_r_symm hR)

  let H_of (x : α) : Set S := L_of x ∩ R_of x

  have h_H_idem : ∀ x, ∃ e ∈ H_of x, e * e = e := by
    intro x
    by_cases h_inner : ¬ is_min x ∧ ¬ is_max x
    · obtain ⟨h_not_min, h_not_max⟩ := h_inner
      have hy : ∃ y, y < x := by contrapose! h_not_min; exact h_not_min
      have hz : ∃ z, x < z := by contrapose! h_not_max; exact h_not_max

      have ha : σ.σ (Classical.choose hy) x ∈ D := h_range _ _ (Classical.choose_spec hy)
      have hb : σ.σ x (Classical.choose hz) ∈ D := h_range _ _ (Classical.choose_spec hz)
      have hab : σ.σ (Classical.choose hy) x * σ.σ x (Classical.choose hz) ∈ D := by
        rw [σ.prop _ _ _ (Classical.choose_spec hy) (Classical.choose_spec hz)]
        exact h_range _ _ (lt_trans (Classical.choose_spec hy) (Classical.choose_spec hz))

      obtain ⟨_, ⟨e, _, he_idem, hLe, hRe⟩⟩ :=
        mul_mem_green_d_properties hD (σ.σ (Classical.choose hy) x) (σ.σ x (Classical.choose hz)) ha hb hab

      use e
      refine ⟨⟨?_, ?_⟩, he_idem⟩
      · simp only [L_of, h_not_min, dite_false]
        exact green_l_symm hLe
      · simp only [R_of, h_not_max, dite_false]
        exact green_r_symm hRe

    · sorry

  sorry

end RegularDClassCase
