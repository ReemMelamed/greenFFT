/- Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz -/

import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic
import Mathlib.Order.Max

import Semigroup.Green

/-!
# The Factorization Forest Theorem

This file defines the basic structures for the Factorization Forest Theorem
and proves specific cases (e.g., the group H-class case and regular D-class case).

## Main definitions
* `MultiplicativeLabeling`: A labeling function obeying multiplicative properties.
* `Split`: A function assigning a bounded rank to elements.

## Main statements
* `simon_group_case`: The Factorization Forest Theorem restricted to a group.
* `simon_regular_d_case`: The theorem applied to a regular D-class.

## References
* [T. Colombet, *The Factorization Forest Theorem*][colombet2008]

## Tags
factorization forest, semigroup, green's relations, simon
-/

section SplitDefinitions

variable {S α : Type*} [Semigroup S] [LinearOrder α]

variable {h : ℕ}

/-- A multiplicative labeling over a linearly ordered set into a semigroup,
satisfying the property that `σ x y * σ y z = σ x z`. -/
structure MultiplicativeLabeling (S α : Type*) [Semigroup S] [LinearOrder α] where
  σ : α → α → S
  prop : ∀ x y z : α, x < y → y < z → σ x y * σ y z = σ x z

/-- A split is a function assigning each element of `α` a bounded integer rank in `Fin h`. -/
abbrev Split (α : Type*) (h : ℕ) := α → Fin h

/-- `splitRelation s x y` states that `x` and `y` share the same rank under `s`,
and any element bounded between them has a rank at most that of `x` and `y`. -/
def SplitRelation (s : Split α h) (x y : α) : Prop :=
  s x = s y ∧ ∀ z, min x y ≤ z → z ≤ max x y → s z ≤ s (min x y)

/-- A split function is normalized if
  the minimal element of `α` receives the maximal possible rank. -/
def IsNormalized [Fintype α] [Nonempty α] [Nonempty (Fin h)] (s : Split α h) : Prop :=
  let min_α := Finset.min' Finset.univ Finset.univ_nonempty
  s min_α = Finset.max' Finset.univ Finset.univ_nonempty

/-- `IsRamsey L s` holds if for any two elements sharing the same rank under the split relation,
their labeling acts as an idempotent. -/
def IsRamsey (L : MultiplicativeLabeling S α) (s : Split α h) : Prop :=
  ∀ x y : α, x < y → SplitRelation s x y → L.σ x y * L.σ x y = L.σ x y

/-- The relation induced by a split function is an equivalence relation. -/
theorem splitRelation_equiv (s : Split α h) : Equivalence (SplitRelation s) := by
  constructor <;> grind [SplitRelation]

end SplitDefinitions


section GroupCase

variable {G α : Type*} [Group G] [Fintype G] [LinearOrder α] [Fintype α] [Nonempty α]

open Classical in
/-- The Factorization Forest Theorem restricted to a group.
There exists a normalized split function acting as a Ramsey split for the group labeling. -/
lemma simon_group_case (σ : MultiplicativeLabeling G α) :
    ∃ (s : Split α (Fintype.card G)), IsNormalized s ∧ IsRamsey σ s := by
  let size_G := Fintype.card G
  let x₀ : α := Finset.min' .univ Finset.univ_nonempty
  have h_size_cast : size_G - 1 + 1 = size_G := by grind [Fintype.card_pos]
  haveI : Nonempty (Fin size_G) := by grind [Fintype.card_pos, Fin.pos_iff_nonempty]
  let max_rank : Fin size_G := Fin.cast h_size_cast (Fin.last (size_G - 1))
  let raw_equiv := Fintype.equivFin G
  let index_in_enum := raw_equiv.trans (Equiv.swap (raw_equiv 1) max_rank)
  let s : Split α size_G := fun y ↦
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
        have h_temp := congr_arg (fun g ↦ (σ.σ x₀ x)⁻¹ * g) h_mult
        simp only [inv_mul_cancel_left, inv_mul_cancel] at h_temp
        exact h_temp
      simp only [h_res, mul_one]

end GroupCase


section HClassWrapper

variable {S α : Type*} [Semigroup S] [LinearOrder α]

/-- The Factorization Forest Theorem applied to an H-class that forms a group. -/
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
  let σ_H_fun : X → X → H := fun x y ↦
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
/-- The number of elements in a D-class that are H-related to an idempotent.
Returns 1 for non-regular D-classes as a default. -/
noncomputable def nD (D : Set S) : ℕ :=
  if IsRegularDClass D then
    (Finset.univ.filter (fun x ↦
      x ∈ D ∧ ∃ e ∈ D, e * e = e ∧ IsGreenH x e
    )).card
  else
    1

/-- The value `nD D` is strictly positive for any Green's D-class. -/
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

/-- Instance providing that the set of available ranks for a D-class is inhabited. -/
instance (D : Set S) (hD : ∃ x, D = IsGreenD.eqvClass x) : Nonempty (Fin (nD D)) :=
  Fin.pos_iff_nonempty.mp (nD_pos D hD)

end nD



section RegularDClassCase

variable {S α : Type*} [Semigroup S] [LinearOrder α]

/-- Context bundling the conditions required to construct a Simon split for a regular D-class. -/
structure SimonContext (S α : Type*) [Semigroup S] [Fintype S] [LinearOrder α] where
  σ : MultiplicativeLabeling S α
  D : Set S
  x₀ : S
  hx₀ : D = IsGreenD.eqvClass x₀
  hReg : IsRegularDClass D
  h_range : ∀ x y, x < y → σ.σ x y ∈ D

open Classical in
/-- Chooses an element strictly smaller than `x`, given that `x` is not minimal. -/
noncomputable def getLt (x : α) (h : ¬ IsMin x) : α :=
  Classical.choose (not_isMin_iff.mp h)

/-- The chosen element is strictly less than `x`. -/
lemma getLt_prop (x : α) (h : ¬ IsMin x) : getLt x h < x :=
  Classical.choose_spec (not_isMin_iff.mp h)

open Classical in
/-- Chooses an element strictly greater than `x`, given that `x` is not maximal. -/
noncomputable def getGt (x : α) (h : ¬ IsMax x) : α :=
  Classical.choose (not_isMax_iff.mp h)

/-- The chosen element is strictly greater than `x`. -/
lemma getGt_prop (x : α) (h : ¬ IsMax x) : x < getGt x h :=
  Classical.choose_spec (not_isMax_iff.mp h)


section WithFintypeS
variable [Fintype S]

open Classical in
/-- Computes the target Green's L-class for the element `x` based on the Simon context. -/
noncomputable def lOf (ctx : SimonContext S α) (x : α) : Set S :=
  if h_min : IsMin x then
    if h_max : IsMax x then
      IsGreenL.eqvClass ctx.x₀
    else
      have ha_D : ctx.σ.σ x (getGt x h_max) ∈ ctx.D := ctx.h_range x _ (getGt_prop x h_max)
      have h_exists := exists_idempotent_in_greenR_of_regular (ctx.hReg _ ha_D)
      IsGreenL.eqvClass (Classical.choose h_exists)
  else
    IsGreenL.eqvClass (ctx.σ.σ (getLt x h_min) x)

open Classical in
/-- Computes the target Green's R-class for the element `x` based on the Simon context. -/
noncomputable def rOf (ctx : SimonContext S α) (x : α) : Set S :=
  if h_max : IsMax x then
    if h_min : IsMin x then
      have ha_D : ctx.x₀ ∈ ctx.D := by rw [ctx.hx₀]; exact IsGreenD.refl ctx.x₀
      have h_exists := exists_idempotent_in_greenL_of_regular (ctx.hReg _ ha_D)
      IsGreenR.eqvClass (Classical.choose h_exists)
    else
      have ha_D : ctx.σ.σ (getLt x h_min) x ∈ ctx.D := ctx.h_range _ x (getLt_prop x h_min)
      have h_exists := exists_idempotent_in_greenL_of_regular (ctx.hReg _ ha_D)
      IsGreenR.eqvClass (Classical.choose h_exists)
  else
    IsGreenR.eqvClass (ctx.σ.σ x (getGt x h_max))

/-- Computes the target Green's H-class for the element `x`, defined as the intersection
of its assigned L-class and R-class. -/
noncomputable def hOf (ctx : SimonContext S α) (x : α) : Set S :=
  lOf ctx x ∩ rOf ctx x

/-- The chosen L-class is well-defined and depends
  only on the elements strictly smaller than `x`. -/
lemma lOf_well_defined (ctx : SimonContext S α) (x y1 y2 : α) (_h_not_min : ¬ IsMin x)
    (hy1 : y1 < x) (hy2 : y2 < x) :
    IsGreenL.eqvClass (ctx.σ.σ y1 x) = IsGreenL.eqvClass (ctx.σ.σ y2 x) := by
  wlog h_le : y1 ≤ y2 generalizing y1 y2 hy1 hy2
  · exact (this y2 y1 hy2 hy1 (le_of_lt (not_le.mp h_le))).symm
  · rcases h_le.eq_or_lt with rfl | h_lt
    · rfl
    · have h_prod : ctx.σ.σ y1 x = ctx.σ.σ y1 y2 * ctx.σ.σ y2 x :=
        (ctx.σ.prop y1 y2 x h_lt hy2).symm
      have h12 : ctx.σ.σ y1 y2 ∈ ctx.D := ctx.h_range y1 y2 h_lt
      have h2x : ctx.σ.σ y2 x ∈ ctx.D := ctx.h_range y2 x hy2
      have h1x : ctx.σ.σ y1 x ∈ ctx.D := ctx.h_range y1 x hy1
      have h_lem := mul_mem_isGreenD_eqvClass_properties ⟨ctx.x₀, ctx.hx₀⟩
        (ctx.σ.σ y1 y2) (ctx.σ.σ y2 x) h12 h2x (h_prod ▸ h1x)
      have hL_raw := h_lem.1.2
      have hL : IsGreenL (ctx.σ.σ y2 x) (ctx.σ.σ y1 x) := h_prod ▸ hL_raw
      ext z
      constructor
      · intro hz; exact IsGreenL.trans hz (IsGreenL.symm hL)
      · intro hz; exact IsGreenL.trans hz hL

/-- The chosen R-class is well-defined and depends
  only on the elements strictly greater than `x`. -/
lemma rOf_well_defined (ctx : SimonContext S α) (x y1 y2 : α) (_h_not_max : ¬ IsMax x)
    (hy1 : x < y1) (hy2 : x < y2) :
    IsGreenR.eqvClass (ctx.σ.σ x y1) = IsGreenR.eqvClass (ctx.σ.σ x y2) := by
  wlog h_le : y1 ≤ y2 generalizing y1 y2 hy1 hy2
  · exact (this y2 y1 hy2 hy1 (le_of_lt (not_le.mp h_le))).symm
  · rcases h_le.eq_or_lt with rfl | h_lt
    · rfl
    · have h_prod : ctx.σ.σ x y1 * ctx.σ.σ y1 y2 = ctx.σ.σ x y2 := ctx.σ.prop x y1 y2 hy1 h_lt
      have hx1 : ctx.σ.σ x y1 ∈ ctx.D := ctx.h_range x y1 hy1
      have h12 : ctx.σ.σ y1 y2 ∈ ctx.D := ctx.h_range y1 y2 h_lt
      have hx2 : ctx.σ.σ x y2 ∈ ctx.D := ctx.h_range x y2 hy2
      have h_lem := mul_mem_isGreenD_eqvClass_properties ⟨ctx.x₀, ctx.hx₀⟩
        (ctx.σ.σ x y1) (ctx.σ.σ y1 y2) hx1 h12 (h_prod.symm ▸ hx2)
      have hR_raw := h_lem.1.1
      have hR : IsGreenR (ctx.σ.σ x y1) (ctx.σ.σ x y2) := h_prod ▸ hR_raw
      ext z
      constructor
      · intro hz; exact IsGreenR.trans hz hR
      · intro hz; exact IsGreenR.trans hz (IsGreenR.symm hR)

/-- An element's assigned H-class contains at least one idempotent element. -/
lemma hOf_has_idempotent (ctx : SimonContext S α) (x : α) :
    ∃ e_id : S, e_id ∈ hOf ctx x ∧ e_id * e_id = e_id := by
  dsimp [hOf]
  by_cases h_min : IsMin x
  · by_cases h_max : IsMax x
    · have ha_D : ctx.x₀ ∈ ctx.D := by rw [ctx.hx₀]; exact IsGreenD.refl ctx.x₀
      have h_exists := exists_idempotent_in_greenL_of_regular (ctx.hReg _ ha_D)
      let ex : S := Classical.choose h_exists
      have he_prop := Classical.choose_spec h_exists
      use ex
      refine ⟨⟨?_, ?_⟩, he_prop.right⟩
      · simp only [lOf, h_min, h_max, dite_true]
        exact he_prop.left
      · simp only [rOf, h_max, h_min, dite_true]
        exact IsGreenR.refl ex
    · have ha_D : ctx.σ.σ x (getGt x h_max) ∈ ctx.D := ctx.h_range x _ (getGt_prop x h_max)
      have h_exists := exists_idempotent_in_greenR_of_regular (ctx.hReg _ ha_D)
      let ex : S := Classical.choose h_exists
      have he_prop := Classical.choose_spec h_exists
      use ex
      refine ⟨⟨?_, ?_⟩, he_prop.right⟩
      · simp only [lOf, h_min, h_max, dite_true, dite_false]
        exact IsGreenL.refl ex
      · simp only [rOf, h_max, dite_false]
        exact he_prop.left
  · by_cases h_max : IsMax x
    · have ha_D : ctx.σ.σ (getLt x h_min) x ∈ ctx.D := ctx.h_range _ x (getLt_prop x h_min)
      have h_exists := exists_idempotent_in_greenL_of_regular (ctx.hReg _ ha_D)
      let ex : S := Classical.choose h_exists
      have he_prop := Classical.choose_spec h_exists
      use ex
      refine ⟨⟨?_, ?_⟩, he_prop.right⟩
      · simp only [lOf, h_min, dite_false]
        exact he_prop.left
      · simp only [rOf, h_max, h_min, dite_true, dite_false]
        exact IsGreenR.refl ex
    · have ha : ctx.σ.σ (getLt x h_min) x ∈ ctx.D := ctx.h_range _ _ (getLt_prop x h_min)
      have hb : ctx.σ.σ x (getGt x h_max) ∈ ctx.D := ctx.h_range _ _ (getGt_prop x h_max)
      have hab : ctx.σ.σ (getLt x h_min) x * ctx.σ.σ x (getGt x h_max) ∈ ctx.D := by
        rw [ctx.σ.prop _ _ _ (getLt_prop x h_min) (getGt_prop x h_max)]
        exact ctx.h_range _ _ (lt_trans (getLt_prop x h_min) (getGt_prop x h_max))
      obtain ⟨_, ⟨ex, _, he_idem, hLe, hRe⟩⟩ :=
        mul_mem_isGreenD_eqvClass_properties ⟨ctx.x₀, ctx.hx₀⟩ _ _ ha hb hab
      use ex
      refine ⟨⟨?_, ?_⟩, he_idem⟩
      · simp only [lOf, h_min, dite_false]
        exact IsGreenL.symm hLe
      · simp only [rOf, h_max, dite_false]
        exact IsGreenR.symm hRe

open Classical in
/-- Chooses an idempotent element belonging to the H-class assigned to `x`. -/
noncomputable def eId (ctx : SimonContext S α) (x : α) : S :=
  Classical.choose (hOf_has_idempotent ctx x)

/-- The chosen idempotent `eId ctx x` is indeed an element of `hOf ctx x`. -/
lemma eId_mem (ctx : SimonContext S α) (x : α) : eId ctx x ∈ hOf ctx x :=
  (Classical.choose_spec (hOf_has_idempotent ctx x)).1

/-- The chosen element `eId ctx x` is an idempotent. -/
@[simp] lemma eId_idem (ctx : SimonContext S α) (x : α) : eId ctx x * eId ctx x = eId ctx x :=
  (Classical.choose_spec (hOf_has_idempotent ctx x)).2

/-- The H-class of `z` is exactly the H-class of its chosen idempotent. -/
lemma hOf_eq_class (ctx : SimonContext S α) (z : α) :
    hOf ctx z = IsGreenH.eqvClass (eId ctx z) := by
  ext w
  have he := eId_mem ctx z
  dsimp only [hOf, lOf, rOf, IsGreenH.eqvClass,
              IsGreenL.eqvClass, IsGreenR.eqvClass, IsGreenH] at he ⊢
  rw [Set.mem_inter_iff] at he
  split_ifs at he ⊢
  all_goals {
    change (_ ∧ _) at he
    change (_ ∧ _) ↔ _
    grind [IsGreenL.trans, IsGreenL.symm, IsGreenR.trans, IsGreenR.symm]
  }

/-- Under certain conditions, `σ mz z` behaves multiplicatively with idempotents. -/
lemma sigma_props (ctx : SimonContext S α) (z mz : α) (h_mz : mz < z)
    (hm_H : hOf ctx mz = hOf ctx z) :
    eId ctx z * ctx.σ.σ mz z * eId ctx z = ctx.σ.σ mz z ∧
    IsGreenH (ctx.σ.σ mz z) (eId ctx z) := by
  have hn_min : ¬ IsMin z := fun h ↦ lt_irrefl mz (lt_of_lt_of_le h_mz (h (le_of_lt h_mz)))
  have hn_max : ¬ IsMax mz := fun h ↦ lt_irrefl z (lt_of_le_of_lt (h (le_of_lt h_mz)) h_mz)
  have hL : IsGreenL (eId ctx z) (ctx.σ.σ mz z) := by
    have h := (eId_mem ctx z).1
    rw [lOf, dif_neg hn_min, lOf_well_defined ctx z _ mz hn_min (getLt_prop z hn_min) h_mz] at h
    exact h
  have hR : IsGreenR (eId ctx z) (ctx.σ.σ mz z) := by
    have h := (hm_H ▸ eId_mem ctx z).2
    rw [rOf, dif_neg hn_max, rOf_well_defined ctx mz _ z hn_max (getGt_prop mz hn_max) h_mz] at h
    exact h
  have hH : IsGreenH (ctx.σ.σ mz z) (eId ctx z) := ⟨IsGreenL.symm hL, IsGreenR.symm hR⟩
  grind [mul_eq_self_of_isGreenH_idempotent hH (eId_idem ctx z), mul_assoc]


section WithFintypeAlpha
variable [Fintype α]

/-- A subtype of elements in `D` that are H-related to an idempotent in `D`. -/
abbrev GDType (D : Set S) :=
  { y : S // y ∈ D ∧ ∃ e ∈ D, e * e = e ∧ IsGreenH y e }

open Classical in
/-- The coloring function mapping an element `x` to a subtype
representing its value and properties in the D-class. -/
noncomputable def fColoring (ctx : SimonContext S α) (x : α) : GDType ctx.D :=
  let m_class := Finset.univ.filter (fun y ↦ hOf ctx y = hOf ctx x)
  have hm_nonempty : m_class.Nonempty := ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, rfl⟩⟩
  let m := Finset.min' m_class hm_nonempty
  if h_mx : m < x then
      let val := eId ctx x * ctx.σ.σ m x * eId ctx x
      have h_val_in : val ∈ ctx.D ∧ ∃ e' ∈ ctx.D, e' * e' = e' ∧ IsGreenH val e' := by
        have hm_in := Finset.min'_mem m_class hm_nonempty
        have hm_H : hOf ctx m = hOf ctx x := (Finset.mem_filter.mp hm_in).2
        have h_not_min_x : ¬ IsMin x :=
          fun h ↦ lt_irrefl m (lt_of_lt_of_le h_mx (h (le_of_lt h_mx)))
        have h_L_mx : lOf ctx x = IsGreenL.eqvClass (ctx.σ.σ m x) := by
          dsimp only [lOf]
          rw [dif_neg h_not_min_x]
          exact lOf_well_defined ctx x (getLt x h_not_min_x) m
            h_not_min_x (getLt_prop x h_not_min_x) h_mx
        have he_L_sig : IsGreenL (eId ctx x) (ctx.σ.σ m x) := by
          have h1 : eId ctx x ∈ lOf ctx x := (eId_mem ctx x).1
          rwa [h_L_mx] at h1
        have h_not_max_m : ¬ IsMax m :=
          fun h ↦ lt_irrefl x (lt_of_le_of_lt (h (le_of_lt h_mx)) h_mx)
        have h_R_m : rOf ctx m = IsGreenR.eqvClass (ctx.σ.σ m x) := by
          dsimp only [rOf]
          rw [dif_neg h_not_max_m]
          exact rOf_well_defined ctx m (getGt m h_not_max_m) x
            h_not_max_m (getGt_prop m h_not_max_m) h_mx
        have he_R_sig : IsGreenR (eId ctx x) (ctx.σ.σ m x) := by
          have hx_in_H : eId ctx x ∈ hOf ctx m := hm_H ▸ eId_mem ctx x
          have h1 : eId ctx x ∈ rOf ctx m := hx_in_H.2
          rwa [h_R_m] at h1
        have he_H_sig : IsGreenH (eId ctx x) (ctx.σ.σ m x) := ⟨he_L_sig, he_R_sig⟩
        have h_sig_H_e : IsGreenH (ctx.σ.σ m x) (eId ctx x) := IsGreenH.symm he_H_sig
        have h_class_eq : ∃ a, IsGreenH.eqvClass (eId ctx x) = IsGreenH.eqvClass a :=
          ⟨eId ctx x, rfl⟩
        have h_group_or := isGroup_isGreenH_eqvClass_iff_idempotent
          (IsGreenH.eqvClass (eId ctx x)) h_class_eq
        have h_group : ∀ u v, u ∈ IsGreenH.eqvClass (eId ctx x) →
            v ∈ IsGreenH.eqvClass (eId ctx x) → u * v ∈ IsGreenH.eqvClass (eId ctx x) := by
          rcases h_group_or with h_empty | ⟨e', he'H, he'idem, h_mul⟩
          · have h_ee_not := h_empty (eId ctx x) (eId ctx x)
              (IsGreenH.refl (eId ctx x)) (IsGreenH.refl (eId ctx x))
            rw [eId_idem ctx x] at h_ee_not
            exact False.elim (h_ee_not (IsGreenH.refl (eId ctx x)))
          · exact h_mul
        have h_sig_He : ctx.σ.σ m x ∈ IsGreenH.eqvClass (eId ctx x) := h_sig_H_e
        have he_He : eId ctx x ∈ IsGreenH.eqvClass (eId ctx x) := IsGreenH.refl (eId ctx x)
        have h_val_He : val ∈ IsGreenH.eqvClass (eId ctx x) := by
          dsimp only [val]
          have h1 := h_group (eId ctx x) (ctx.σ.σ m x) he_He h_sig_He
          exact h_group (eId ctx x * ctx.σ.σ m x) (eId ctx x) h1 he_He
        have h_val_H_e : IsGreenH val (eId ctx x) := h_val_He
        have h_sig_D : ctx.σ.σ m x ∈ ctx.D := ctx.h_range m x h_mx
        have he_D_sig : IsGreenD (eId ctx x) (ctx.σ.σ m x) :=
          ⟨eId ctx x, IsGreenL.refl (eId ctx x), he_H_sig.right⟩
        have he_D : eId ctx x ∈ ctx.D := by
          rw [ctx.hx₀] at h_sig_D ⊢
          exact IsGreenD.trans he_D_sig h_sig_D
        have hval_D_e : IsGreenD val (eId ctx x) := ⟨val, IsGreenL.refl val, h_val_H_e.right⟩
        have h_val_D : val ∈ ctx.D := by
          rw [ctx.hx₀] at he_D ⊢
          exact IsGreenD.trans hval_D_e he_D
        exact ⟨h_val_D, eId ctx x, he_D, eId_idem ctx x, h_val_H_e⟩
      ⟨val, h_val_in⟩
  else
      have h_e_in : eId ctx x ∈ ctx.D ∧ ∃ e' ∈ ctx.D, e' * e' = e' ∧ IsGreenH (eId ctx x) e' := by
        have he_D : eId ctx x ∈ ctx.D := by
          have he_L : eId ctx x ∈ lOf ctx x := (eId_mem ctx x).1
          by_cases h_min : IsMin x
          · by_cases h_max : IsMax x
            · dsimp only [lOf] at he_L
              rw [dif_pos h_min, dif_pos h_max] at he_L
              rw [ctx.hx₀]
              exact ⟨ctx.x₀, he_L, IsGreenR.refl ctx.x₀⟩
            · let y' := getGt x h_max
              have ha_D : ctx.σ.σ x y' ∈ ctx.D := ctx.h_range x y' (getGt_prop x h_max)
              dsimp only [lOf] at he_L
              rw [dif_pos h_min, dif_neg h_max] at he_L
              have h_ex := exists_idempotent_in_greenR_of_regular (ctx.hReg _ ha_D)
              let e_R : S := Classical.choose h_ex
              have he_R_prop := Classical.choose_spec h_ex
              rw [ctx.hx₀] at ha_D ⊢
              have hD_e_sig : IsGreenD (eId ctx x) (ctx.σ.σ x y') := ⟨e_R, he_L, he_R_prop.left⟩
              exact IsGreenD.trans hD_e_sig ha_D
          · let y' := getLt x h_min
            dsimp only [lOf] at he_L
            rw [dif_neg h_min] at he_L
            have ha_D : ctx.σ.σ y' x ∈ ctx.D := ctx.h_range y' x (getLt_prop x h_min)
            rw [ctx.hx₀] at ha_D ⊢
            have hD_e_sig : IsGreenD (eId ctx x) (ctx.σ.σ y' x) :=
              ⟨ctx.σ.σ y' x, he_L, IsGreenR.refl _⟩
            exact IsGreenD.trans hD_e_sig ha_D
        exact ⟨he_D, eId ctx x, he_D, eId_idem ctx x, IsGreenH.refl (eId ctx x)⟩
      ⟨eId ctx x, h_e_in⟩

open Classical in
/-- The element returned by `fColoring` belongs to the correct Green's H-class. -/
lemma fColoring_isGreenH (ctx : SimonContext S α) (z : α) :
    IsGreenH (fColoring ctx z).val (eId ctx z) := by
  let m_class := Finset.univ.filter (fun w ↦ hOf ctx w = hOf ctx z)
  have hm_nonempty : m_class.Nonempty := ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ z, rfl⟩⟩
  let mz := Finset.min' m_class hm_nonempty
  have hm_in := Finset.min'_mem m_class hm_nonempty
  have hm_H : hOf ctx mz = hOf ctx z := (Finset.mem_filter.mp hm_in).2
  have h_val : (fColoring ctx z).val =
      if h_lt : mz < z then eId ctx z * ctx.σ.σ mz z * eId ctx z else eId ctx z := by
    dsimp only [fColoring]; split_ifs <;> rfl
  rw [h_val]
  split_ifs with h_mz
  · have h_props := sigma_props ctx z mz h_mz hm_H
    rw [h_props.1]
    exact h_props.2
  · exact IsGreenH.refl (eId ctx z)


section WithNonemptyAlpha
variable [Nonempty α]

open Classical in
/-- The Factorization Forest Theorem applied to a regular D-class.
Given a multiplicative labeling `σ` taking values in a regular D-class `D`,
there exists a normalized split function into `nD D` ranks that acts as a Ramsey split for `σ`. -/
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
  have h_card_G_D : Fintype.card (GDType D) = nD D := by
    dsimp [nD]; rw [if_pos hReg]; exact Fintype.card_subtype _
  have h_card_pos : 0 < Fintype.card (GDType D) := by
    rw [h_card_G_D]; exact Fin.pos_iff_nonempty.mpr (Fin.pos_iff_nonempty.mp (nD_pos D ⟨x₀, hx₀⟩))
  let max_rank : Fin (nD D) := Fin.cast h_card_G_D
    (Fin.cast (Nat.sub_add_cancel h_card_pos) (Fin.last (Fintype.card (GDType D) - 1)))
  let equiv_G_D_Fin : GDType D ≃ Fin (nD D) :=
    (Fintype.equivFin _).trans (Equiv.cast (congrArg Fin h_card_G_D))
  let alpha_min : α := Finset.min' Finset.univ Finset.univ_nonempty
  let index_map := equiv_G_D_Fin.trans
    (Equiv.swap (equiv_G_D_Fin (fColoring ctx alpha_min)) max_rank)
  let s : Split α (nD D) := fun y ↦ index_map (fColoring ctx y)
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
      have h_max_val : (max_rank : ℕ) = nD D - 1 := by
        simp only [Fin.cast_cast, Nat.succ_eq_add_one, Nat.reduceAdd,
          Fin.val_cast, Fin.val_last, max_rank]
        rw [h_card_G_D]
      rw [h_max_val]
      exact Nat.le_pred_of_lt y.is_lt
  · intros x y hlt hsr
    unfold SplitRelation at hsr
    have h_f_eq : fColoring ctx x = fColoring ctx y := Equiv.injective index_map hsr.left
    have h_val_eq : (fColoring ctx x).val = (fColoring ctx y).val := congrArg Subtype.val h_f_eq
    have h_fz_H_e := fColoring_isGreenH ctx x
    have h_fy_H_ey := fColoring_isGreenH ctx y
    have he_H_ey : IsGreenH (eId ctx x) (eId ctx y) := by
      have h1 : IsGreenH (eId ctx x) (fColoring ctx x).val := IsGreenH.symm h_fz_H_e
      exact IsGreenH.trans h1 (h_val_eq ▸ h_fy_H_ey)
    have he_eq_ey : eId ctx x = eId ctx y :=
      eq_of_isGreenH_of_idempotent he_H_ey (eId_idem ctx x) (eId_idem ctx y)
    let m_class_x := Finset.univ.filter (fun z ↦ hOf ctx z = hOf ctx x)
    let m_class_y := Finset.univ.filter (fun z ↦ hOf ctx z = hOf ctx y)
    have hm_nonempty_x : m_class_x.Nonempty := ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, rfl⟩⟩
    have hm_nonempty_y : m_class_y.Nonempty := ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ y, rfl⟩⟩
    let mx := Finset.min' m_class_x hm_nonempty_x
    let my := Finset.min' m_class_y hm_nonempty_y
    have h_same_H : hOf ctx x = hOf ctx y := by
      rw [hOf_eq_class ctx x, hOf_eq_class ctx y, he_eq_ey]
    have h_mx_eq_my : mx = my := by
      have h_class_eq : m_class_x = m_class_y := by
        ext z
        simp only [m_class_x, m_class_y, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h ↦ h.trans h_same_H, fun h ↦ h.trans h_same_H.symm⟩
      apply le_antisymm
      · have h_my_in_x : my ∈ m_class_x := by
          rw [h_class_eq]; exact Finset.min'_mem m_class_y hm_nonempty_y
        exact Finset.min'_le m_class_x my h_my_in_x
      · have h_mx_in_y : mx ∈ m_class_y := by
          rw [← h_class_eq]; exact Finset.min'_mem m_class_x hm_nonempty_x
        exact Finset.min'_le m_class_y mx h_mx_in_y
    have h_ese_eq_e : eId ctx x * σ.σ x y * eId ctx x = eId ctx x := by
      by_cases h_mx : mx < x
      · have h_mem_x := Finset.min'_mem m_class_x hm_nonempty_x
        have hm_H : hOf ctx mx = hOf ctx x := (Finset.mem_filter.mp h_mem_x).2
        have h_props_x := sigma_props ctx x mx h_mx hm_H
        have h_val_x : (fColoring ctx x).val =
            if h_lt : mx < x then eId ctx x * σ.σ mx x * eId ctx x else eId ctx x := by
          dsimp only [fColoring]; split_ifs <;> rfl
        have h_fx : (fColoring ctx x).val = σ.σ mx x := by
          rw [h_val_x, dif_pos h_mx]; exact h_props_x.1
        have h_my : my < y := by rw [← h_mx_eq_my]; exact lt_trans h_mx hlt
        have h_mem_y := Finset.min'_mem m_class_y hm_nonempty_y
        have hm_Hy : hOf ctx my = hOf ctx y := (Finset.mem_filter.mp h_mem_y).2
        have h_props_y := sigma_props ctx y my h_my hm_Hy
        have h_val_y : (fColoring ctx y).val =
            if h_lt : my < y then eId ctx y * σ.σ my y * eId ctx y else eId ctx y := by
          dsimp only [fColoring]; split_ifs <;> rfl
        have h_fy : (fColoring ctx y).val = σ.σ my y := by
          rw [h_val_y, dif_pos h_my]; exact h_props_y.1
        have hid_mx_mul := mul_eq_self_of_isGreenH_idempotent h_props_x.2 (eId_idem ctx x)
        have hid_my_mul := mul_eq_self_of_isGreenH_idempotent h_props_y.2 (eId_idem ctx y)
        have h_v_eq : σ.σ mx x * σ.σ x y * eId ctx x = σ.σ mx x := by
          grind [hid_mx_mul.1, hid_mx_mul.2, σ.prop mx x y h_mx hlt,
                hid_my_mul.1, hid_my_mul.2, mul_assoc]
        have he_L_sig : IsGreenL (eId ctx x) (σ.σ mx x) := IsGreenL.symm h_props_x.2.left
        rcases he_L_sig.left with heq | ⟨u, hu⟩
        · calc eId ctx x * σ.σ x y * eId ctx x = σ.σ mx x * σ.σ x y * eId ctx x := by rw [heq]
            _ = σ.σ mx x := h_v_eq
            _ = eId ctx x := heq.symm
        · calc eId ctx x * σ.σ x y * eId ctx x =
                (u * σ.σ mx x) * σ.σ x y * eId ctx x := by rw [hu]
            _ = u * (σ.σ mx x * σ.σ x y * eId ctx x) := by simp only [mul_assoc]
            _ = u * σ.σ mx x := by rw [h_v_eq]
            _ = eId ctx x := hu.symm
      · have h_x_le_mx : x ≤ mx := not_lt.mp h_mx
        have hx_in_mx : x ∈ m_class_x := Finset.mem_filter.mpr ⟨Finset.mem_univ x, rfl⟩
        have h_mx_le_x : mx ≤ x := Finset.min'_le m_class_x x hx_in_mx
        have h_mx_eq : mx = x := le_antisymm h_mx_le_x h_x_le_mx
        have h_val_x : (fColoring ctx x).val =
            if h_lt : mx < x then eId ctx x * σ.σ mx x * eId ctx x else eId ctx x := by
          dsimp only [fColoring]; split_ifs <;> rfl
        have h_fx : (fColoring ctx x).val = eId ctx x := by rw [h_val_x, dif_neg h_mx]
        have h_my : my < y := by rw [← h_mx_eq_my, h_mx_eq]; exact hlt
        have h_mem_y := Finset.min'_mem m_class_y hm_nonempty_y
        have hm_Hy : hOf ctx my = hOf ctx y := (Finset.mem_filter.mp h_mem_y).2
        have h_props_y := sigma_props ctx y my h_my hm_Hy
        have h_val_y : (fColoring ctx y).val =
            if h_lt : my < y then eId ctx y * σ.σ my y * eId ctx y else eId ctx y := by
          dsimp only [fColoring]; split_ifs <;> rfl
        have h_fy : (fColoring ctx y).val = σ.σ my y := by
          rw [h_val_y, dif_pos h_my]; exact h_props_y.1
        have hid_my_mul := mul_eq_self_of_isGreenH_idempotent h_props_y.2 (eId_idem ctx y)
        calc eId ctx x * σ.σ x y * eId ctx x =
              eId ctx y * σ.σ my y * eId ctx y := by rw [← he_eq_ey, ← h_mx_eq_my, h_mx_eq]
          _ = (eId ctx y * σ.σ my y) * eId ctx y := by simp only [mul_assoc]
          _ = σ.σ my y * eId ctx y := by rw [hid_my_mul.2]
          _ = σ.σ my y := hid_my_mul.1
          _ = (fColoring ctx y).val := h_fy.symm
          _ = (fColoring ctx x).val := h_val_eq.symm
          _ = eId ctx x := h_fx
    have h_sig_H : IsGreenH (σ.σ x y) (eId ctx x) := by
      have h_not_min_y : ¬ IsMin y := fun h ↦ lt_irrefl x (lt_of_lt_of_le hlt (h (le_of_lt hlt)))
      have h_L_y : lOf ctx y = IsGreenL.eqvClass (σ.σ x y) := by
        dsimp only [lOf]; rw [dif_neg h_not_min_y]
        exact lOf_well_defined ctx y (getLt y h_not_min_y) x
          h_not_min_y (getLt_prop y h_not_min_y) hlt
      have hex_in_Hy : eId ctx x ∈ hOf ctx y := h_same_H ▸ eId_mem ctx x
      have he_L : eId ctx x ∈ lOf ctx y := hex_in_Hy.1
      have he_L_mem : IsGreenL (eId ctx x) (σ.σ x y) := by rwa [h_L_y] at he_L
      have h_not_max_x : ¬ IsMax x := fun h ↦ lt_irrefl y (lt_of_le_of_lt (h (le_of_lt hlt)) hlt)
      have h_R_x : rOf ctx x = IsGreenR.eqvClass (σ.σ x y) := by
        dsimp only [rOf]; rw [dif_neg h_not_max_x]
        exact rOf_well_defined ctx x (getGt x h_not_max_x) y
          h_not_max_x (getGt_prop x h_not_max_x) hlt
      have he_R : eId ctx x ∈ rOf ctx x := (eId_mem ctx x).2
      have he_R_mem : IsGreenR (eId ctx x) (σ.σ x y) := by rwa [h_R_x] at he_R
      exact IsGreenH.symm ⟨he_L_mem, he_R_mem⟩
    have h_final_sigma : σ.σ x y = eId ctx x := by
      have h_sig_id := mul_eq_self_of_isGreenH_idempotent h_sig_H (eId_idem ctx x)
      calc σ.σ x y = eId ctx x * σ.σ x y := h_sig_id.2.symm
        _ = eId ctx x * (σ.σ x y * eId ctx x) := congrArg (fun w ↦ eId ctx x * w) h_sig_id.1.symm
        _ = (eId ctx x * σ.σ x y) * eId ctx x := (mul_assoc _ _ _).symm
        _ = eId ctx x * σ.σ x y * eId ctx x := by simp only [mul_assoc]
        _ = eId ctx x := h_ese_eq_e
    rw [h_final_sigma]
    exact eId_idem ctx x

end WithNonemptyAlpha
end WithFintypeAlpha
end WithFintypeS
end RegularDClassCase
