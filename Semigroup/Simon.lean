/- Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz -/

import Mathlib.Data.Fintype.Card
import Mathlib.Order.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic
import Mathlib.Order.Max

import Semigroup.GreensRelations.Defs
import Semigroup.GreensRelations.Classes
import Semigroup.GreensRelations.Theorems

/-!
# The Factorization Forest Theorem

This file defines the basic structures for the Factorization Forest Theorem
and proves specific cases (e.g., the group H-class case and regular D-class case).

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

/-- The Factorization Forest Theorem restricted to a group.
There exists a normalized split function acting as a Ramsey split for the group labeling. -/
lemma simon_group_case (σ : MultiplicativeLabeling G α) :
    ∃ (s : Split α (Fintype.card G)), IsNormalized s ∧ IsRamsey σ s := by
  classical
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
      have h_res : σ.σ x y = 1 := mul_left_cancel (by rw [h_mult, h_vals_eq, mul_one])
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
    exact ⟨heD, e, heD, he_idem, IsGreenH.refl e⟩
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

section WithFintypeS
variable [Fintype S]

open Classical in
/-- Computes the target Green's L-class for the element `x` based on the Simon context. -/
noncomputable def lOf (ctx : SimonContext S α) (x : α) : Set S :=
  if h_min : IsMin x then
    if h_max : IsMax x then
      IsGreenL.eqvClass ctx.x₀
    else
      have ha_D : ctx.σ.σ x (choose (not_isMax_iff.mp h_max)) ∈ ctx.D :=
        ctx.h_range x _ (choose_spec (not_isMax_iff.mp h_max))
      IsGreenL.eqvClass (choose (MulSeq.exists_idempotent_in_greenR_of_regular (ctx.hReg _ ha_D)))
  else
    IsGreenL.eqvClass (ctx.σ.σ (choose (not_isMin_iff.mp h_min)) x)

open Classical in
/-- Computes the target Green's R-class for the element `x` based on the Simon context. -/
noncomputable def rOf (ctx : SimonContext S α) (x : α) : Set S :=
  if h_max : IsMax x then
    if h_min : IsMin x then
      have ha_D : ctx.x₀ ∈ ctx.D := by
        rw [ctx.hx₀]
        exact IsGreenD.refl ctx.x₀
      IsGreenR.eqvClass (choose (MulSeq.exists_idempotent_in_greenL_of_regular (ctx.hReg _ ha_D)))
    else
      have ha_D : ctx.σ.σ (choose (not_isMin_iff.mp h_min)) x ∈ ctx.D :=
        ctx.h_range _ x (choose_spec (not_isMin_iff.mp h_min))
      IsGreenR.eqvClass (choose (MulSeq.exists_idempotent_in_greenL_of_regular (ctx.hReg _ ha_D)))
  else
    IsGreenR.eqvClass (ctx.σ.σ x (choose (not_isMax_iff.mp h_max)))

/-- Computes the target Green's H-class for the element `x`, defined as the intersection
of its assigned L-class and R-class. -/
noncomputable def hOf (ctx : SimonContext S α) (x : α) : Set S :=
  lOf ctx x ∩ rOf ctx x

/-- The chosen L-class is well-defined and depends only
    on the elements strictly smaller than `x`. -/
lemma lOf_well_defined (ctx : SimonContext S α) (x y1 y2 : α)
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
      have h_lem :=
        mul_mem_isGreenD_eqvClass_properties ⟨ctx.x₀, ctx.hx₀⟩ _ _ h12 h2x (h_prod ▸ h1x)
      have hL : IsGreenL (ctx.σ.σ y2 x) (ctx.σ.σ y1 x) := h_prod ▸ h_lem.1.2
      ext z
      exact ⟨fun hz ↦ IsGreenL.trans hz (IsGreenL.symm hL), fun hz ↦ IsGreenL.trans hz hL⟩

/-- The chosen R-class is well-defined and depends only
    on the elements strictly greater than `x`. -/
lemma rOf_well_defined (ctx : SimonContext S α) (x y1 y2 : α)
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
      have h_lem :=
        mul_mem_isGreenD_eqvClass_properties ⟨ctx.x₀, ctx.hx₀⟩ _ _ hx1 h12 (h_prod.symm ▸ hx2)
      have hR : IsGreenR (ctx.σ.σ x y1) (ctx.σ.σ x y2) := h_prod ▸ h_lem.1.1
      ext z
      exact ⟨fun hz ↦ IsGreenR.trans hz hR, fun hz ↦ IsGreenR.trans hz (IsGreenR.symm hR)⟩

open Classical in
/-- An element's assigned H-class contains at least one idempotent element. -/
lemma hOf_has_idempotent (ctx : SimonContext S α) (x : α) :
    ∃ e_id : S, e_id ∈ hOf ctx x ∧ e_id * e_id = e_id := by
  dsimp [hOf]
  by_cases h_min : IsMin x
  · by_cases h_max : IsMax x
    · have ha_D : ctx.x₀ ∈ ctx.D := by
        rw [ctx.hx₀]
        exact IsGreenD.refl ctx.x₀
      have h_exists := MulSeq.exists_idempotent_in_greenL_of_regular (ctx.hReg _ ha_D)
      use choose h_exists
      have he_prop := choose_spec h_exists
      simp [lOf, rOf, h_min, h_max, he_prop, IsGreenR.eqvClass, IsGreenR.refl]
    · have ha_D : ctx.σ.σ x (choose (not_isMax_iff.mp h_max)) ∈ ctx.D :=
        ctx.h_range x _ (choose_spec (not_isMax_iff.mp h_max))
      have h_exists := MulSeq.exists_idempotent_in_greenR_of_regular (ctx.hReg _ ha_D)
      use choose h_exists
      have he_prop := choose_spec h_exists
      simp [lOf, rOf, h_min, h_max, he_prop, IsGreenL.eqvClass, IsGreenL.refl]
  · by_cases h_max : IsMax x
    · have ha_D : ctx.σ.σ (choose (not_isMin_iff.mp h_min)) x ∈ ctx.D :=
        ctx.h_range _ x (choose_spec (not_isMin_iff.mp h_min))
      have h_exists := MulSeq.exists_idempotent_in_greenL_of_regular (ctx.hReg _ ha_D)
      use choose h_exists
      have he_prop := choose_spec h_exists
      simp [lOf, rOf, h_min, h_max, he_prop, IsGreenR.eqvClass, IsGreenR.refl]
    · have ha : ctx.σ.σ (choose (not_isMin_iff.mp h_min)) x ∈ ctx.D :=
        ctx.h_range _ _ (choose_spec (not_isMin_iff.mp h_min))
      have hb : ctx.σ.σ x (choose (not_isMax_iff.mp h_max)) ∈ ctx.D :=
        ctx.h_range _ _ (choose_spec (not_isMax_iff.mp h_max))
      have hab : ctx.σ.σ (choose (not_isMin_iff.mp h_min)) x * ctx.σ.σ x
          (choose (not_isMax_iff.mp h_max)) ∈ ctx.D := by
        rw [ctx.σ.prop _ _ _ (choose_spec (not_isMin_iff.mp h_min))
            (choose_spec (not_isMax_iff.mp h_max))]
        exact ctx.h_range _ _ (lt_trans (choose_spec (not_isMin_iff.mp h_min))
            (choose_spec (not_isMax_iff.mp h_max)))
      obtain ⟨_, ⟨ex, _, he_idem, hLe, hRe⟩⟩ :=
        mul_mem_isGreenD_eqvClass_properties ⟨ctx.x₀, ctx.hx₀⟩ _ _ ha hb hab
      use ex
      simp [lOf, rOf, h_min, h_max, he_idem, IsGreenL.eqvClass,
          IsGreenR.eqvClass, IsGreenL.symm hLe, IsGreenR.symm hRe]

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
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at he ⊢
  split_ifs at he ⊢
  all_goals {
    exact ⟨
      fun ⟨hwL, hwR⟩ => ⟨IsGreenL.trans hwL (IsGreenL.symm he.1),
          IsGreenR.trans hwR (IsGreenR.symm he.2)⟩,
      fun ⟨hwL, hwR⟩ ↦ ⟨IsGreenL.trans hwL he.1, IsGreenR.trans hwR he.2⟩
    ⟩
  }

open Classical in
/-- Under certain conditions, `σ mz z` behaves multiplicatively with idempotents. -/
lemma sigma_props (ctx : SimonContext S α) (z mz : α) (h_mz : mz < z)
    (hm_H : hOf ctx mz = hOf ctx z) :
    eId ctx z * ctx.σ.σ mz z * eId ctx z = ctx.σ.σ mz z ∧
    IsGreenH (ctx.σ.σ mz z) (eId ctx z) := by
  have hn_min : ¬ IsMin z := fun h ↦ lt_irrefl mz (lt_of_lt_of_le h_mz (h (le_of_lt h_mz)))
  have hn_max : ¬ IsMax mz := fun h ↦ lt_irrefl z (lt_of_le_of_lt (h (le_of_lt h_mz)) h_mz)
  have hl_eq : lOf ctx z = IsGreenL.eqvClass (ctx.σ.σ mz z) := by
    rw [lOf, dif_neg hn_min]
    exact lOf_well_defined ctx z _ mz (choose_spec (not_isMin_iff.mp hn_min)) h_mz
  have hr_eq : rOf ctx mz = IsGreenR.eqvClass (ctx.σ.σ mz z) := by
    rw [rOf, dif_neg hn_max]
    exact rOf_well_defined ctx mz _ z (choose_spec (not_isMax_iff.mp hn_max)) h_mz
  have hL : eId ctx z ∈ IsGreenL.eqvClass (ctx.σ.σ mz z) := hl_eq ▸ (eId_mem ctx z).1
  have hR : eId ctx z ∈ IsGreenR.eqvClass (ctx.σ.σ mz z) := hr_eq ▸ (hm_H ▸ eId_mem ctx z).2
  have hH : IsGreenH (ctx.σ.σ mz z) (eId ctx z) := ⟨IsGreenL.symm hL, IsGreenR.symm hR⟩
  grind [MulSeq.mul_eq_self_of_isGreenH_idempotent hH (eId_idem ctx z), mul_assoc]

open Classical in
/-- The chosen idempotent `eId ctx x` belongs to the D-class `ctx.D`. -/
lemma eId_mem_D (ctx : SimonContext S α) (x : α) : eId ctx x ∈ ctx.D := by
  have he_L : eId ctx x ∈ lOf ctx x := (eId_mem ctx x).1
  by_cases h_min : IsMin x
  · by_cases h_max : IsMax x
    · dsimp only [lOf] at he_L
      rw [dif_pos h_min, dif_pos h_max] at he_L
      rw [ctx.hx₀]
      exact ⟨ctx.x₀, he_L, IsGreenR.refl ctx.x₀⟩
    · let y' := choose (not_isMax_iff.mp h_max)
      have ha_D : ctx.σ.σ x y' ∈ ctx.D := ctx.h_range x y' (choose_spec (not_isMax_iff.mp h_max))
      dsimp only [lOf] at he_L
      rw [dif_pos h_min, dif_neg h_max] at he_L
      have h_ex := MulSeq.exists_idempotent_in_greenR_of_regular (ctx.hReg _ ha_D)
      rw [ctx.hx₀] at ha_D ⊢
      exact IsGreenD.trans ⟨choose h_ex, he_L, (choose_spec h_ex).left⟩ ha_D
  · let y' := choose (not_isMin_iff.mp h_min)
    dsimp only [lOf] at he_L
    rw [dif_neg h_min] at he_L
    have ha_D : ctx.σ.σ y' x ∈ ctx.D := ctx.h_range y' x (choose_spec (not_isMin_iff.mp h_min))
    rw [ctx.hx₀] at ha_D ⊢
    exact IsGreenD.trans ⟨ctx.σ.σ y' x, he_L, IsGreenR.refl _⟩ ha_D

open Classical in
/-- Helper lemma for fColoring. -/
lemma fColoring_helper_val_in (ctx : SimonContext S α) (x m : α)
    (h_mx : m < x) (hm_H : hOf ctx m = hOf ctx x) :
    (eId ctx x * ctx.σ.σ m x * eId ctx x) ∈ ctx.D ∧
    ∃ e' ∈ ctx.D, e' * e' = e' ∧ IsGreenH (eId ctx x * ctx.σ.σ m x * eId ctx x) e' := by
  let val := eId ctx x * ctx.σ.σ m x * eId ctx x
  have h_not_min_x : ¬ IsMin x := fun h ↦ lt_irrefl m (lt_of_lt_of_le h_mx (h (le_of_lt h_mx)))
  have h_L_mx : lOf ctx x = IsGreenL.eqvClass (ctx.σ.σ m x) := by
    dsimp only [lOf]
    rw [dif_neg h_not_min_x]
    exact lOf_well_defined ctx x _ m (choose_spec (not_isMin_iff.mp h_not_min_x)) h_mx
  have he_L_sig : IsGreenL (eId ctx x) (ctx.σ.σ m x) := by
    have h1 : eId ctx x ∈ lOf ctx x := (eId_mem ctx x).1
    rwa [h_L_mx] at h1
  have h_not_max_m : ¬ IsMax m := fun h ↦ lt_irrefl x (lt_of_le_of_lt (h (le_of_lt h_mx)) h_mx)
  have h_R_m : rOf ctx m = IsGreenR.eqvClass (ctx.σ.σ m x) := by
    dsimp only [rOf]
    rw [dif_neg h_not_max_m]
    exact rOf_well_defined ctx m _ x (choose_spec (not_isMax_iff.mp h_not_max_m)) h_mx
  have he_R_sig : IsGreenR (eId ctx x) (ctx.σ.σ m x) := by
    have hx_in_H : eId ctx x ∈ hOf ctx m := hm_H ▸ eId_mem ctx x
    have h1 : eId ctx x ∈ rOf ctx m := hx_in_H.2
    rwa [h_R_m] at h1
  have he_H_sig : IsGreenH (eId ctx x) (ctx.σ.σ m x) := ⟨he_L_sig, he_R_sig⟩
  have h_sig_H_e : IsGreenH (ctx.σ.σ m x) (eId ctx x) := IsGreenH.symm he_H_sig
  obtain (h_empty | ⟨_, _, _, h_mul⟩) :=
    isGroup_isGreenH_eqvClass_iff_idempotent (IsGreenH.eqvClass (eId ctx x)) ⟨eId ctx x, rfl⟩
  · have he : eId ctx x ∈ IsGreenH.eqvClass (eId ctx x) := IsGreenH.refl _
    have h_not_in := h_empty _ _ he he
    rw [eId_idem ctx x] at h_not_in
    exact False.elim (h_not_in he)
  have h_group : ∀ u v, u ∈ IsGreenH.eqvClass (eId ctx x) →
      v ∈ IsGreenH.eqvClass (eId ctx x) → u * v ∈ IsGreenH.eqvClass (eId ctx x) := h_mul
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
  have he_D := eId_mem_D ctx x
  have hval_D_e : IsGreenD val (eId ctx x) := ⟨val, IsGreenL.refl val, h_val_H_e.right⟩
  have h_val_D : val ∈ ctx.D := by
    rw [ctx.hx₀] at he_D ⊢
    exact IsGreenD.trans hval_D_e he_D
  exact ⟨h_val_D, eId ctx x, he_D, eId_idem ctx x, h_val_H_e⟩

section WithFintypeAlpha
variable [Fintype α]

open Classical in
/-- The coloring function mapping an element `x` to a subtype
representing its value and properties in the D-class. -/
noncomputable def fColoring (ctx : SimonContext S α) (x : α) :
    { y : S // y ∈ ctx.D ∧ ∃ e ∈ ctx.D, e * e = e ∧ IsGreenH y e } :=
  let m_class := Finset.univ.filter (fun y ↦ hOf ctx y = hOf ctx x)
  have hm_nonempty : m_class.Nonempty := ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, rfl⟩⟩
  let m := Finset.min' m_class hm_nonempty
  if h_mx : m < x then
    have hm_H : hOf ctx m = hOf ctx x :=
      (Finset.mem_filter.mp (Finset.min'_mem m_class hm_nonempty)).2
    ⟨eId ctx x * ctx.σ.σ m x * eId ctx x, fColoring_helper_val_in ctx x m h_mx hm_H⟩
  else
    have h_e_in : eId ctx x ∈ ctx.D ∧ ∃ e' ∈ ctx.D, e' * e' = e' ∧ IsGreenH (eId ctx x) e' := by
      have he_D := eId_mem_D ctx x
      exact ⟨he_D, eId ctx x, he_D, eId_idem ctx x, IsGreenH.refl (eId ctx x)⟩
    ⟨eId ctx x, h_e_in⟩

/-- The element returned by `fColoring` belongs to the correct Green's H-class. -/
lemma fColoring_isGreenH (ctx : SimonContext S α) (z : α) :
    IsGreenH (fColoring ctx z).val (eId ctx z) := by
  classical
  let m_class := Finset.univ.filter (fun w ↦ hOf ctx w = hOf ctx z)
  have hm_nonempty : m_class.Nonempty := ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ z, rfl⟩⟩
  let mz := Finset.min' m_class hm_nonempty
  have hm_H : hOf ctx mz = hOf ctx z := (Finset.mem_filter.mp (Finset.min'_mem _ hm_nonempty)).2
  dsimp only [fColoring]
  split_ifs with h_mz
  · have h_props := sigma_props ctx z mz h_mz hm_H
    change IsGreenH (eId ctx z * ctx.σ.σ mz z * eId ctx z) (eId ctx z)
    rw [h_props.1]
    exact h_props.2
  · exact IsGreenH.refl (eId ctx z)

section WithNonemptyAlpha
variable [Nonempty α]

/-- The Factorization Forest Theorem applied to a regular D-class. -/
lemma simon_regular_d_case
    (σ : MultiplicativeLabeling S α)
    (D : Set S)
    (hD : ∃ x, D = IsGreenD.eqvClass x)
    (hReg : IsRegularDClass D)
    (h_range : ∀ x y, x < y → σ.σ x y ∈ D)
    (h_ne : Nonempty (Fin (nD D)) := Fin.pos_iff_nonempty.mp (nD_pos D hD)) :
    ∃ (s : Split α (nD D)), IsNormalized s ∧ IsRamsey σ s := by
  classical
  obtain ⟨x₀, hx₀⟩ := hD
  let ctx : SimonContext S α := ⟨σ, D, x₀, hx₀, hReg, h_range⟩
  have h_card_G_D : Fintype.card { y : S // y ∈ D ∧ ∃ e ∈ D, e * e = e ∧ IsGreenH y e } = nD D := by
    dsimp [nD]
    rw [if_pos hReg]
    exact Fintype.card_subtype _
  let equiv := (Fintype.equivFin _).trans (Equiv.cast (congrArg Fin h_card_G_D))
  let max_rank : Fin (nD D) := Fin.cast h_card_G_D (Fin.cast (Nat.sub_add_cancel
      (by
        rw [h_card_G_D]
        exact Fin.pos_iff_nonempty.mpr h_ne)) (Fin.last _)
      )
  let index_map := equiv.trans (Equiv.swap (equiv (fColoring ctx
      (Finset.min' Finset.univ Finset.univ_nonempty))) max_rank)
  use fun y ↦ index_map (fColoring ctx y)
  constructor
  · change index_map _ = Finset.max' _ _
    rw [show index_map _ = max_rank by
      dsimp [index_map]
      rw [Equiv.trans_apply, Equiv.swap_apply_left]]
    symm
    rw [Finset.max'_eq_iff]
    exact ⟨Finset.mem_univ _, fun y _ ↦ Fin.le_iff_val_le_val.mpr <| by
      have : (max_rank : ℕ) = nD D - 1 := by simp [max_rank, h_card_G_D]
      omega⟩
  · intros x y hlt hsr
    unfold SplitRelation at hsr
    have h_val_eq : (fColoring ctx x).val = (fColoring ctx y).val :=
      congrArg Subtype.val (Equiv.injective index_map hsr.left)
    have he_eq_ey : eId ctx x = eId ctx y := MulSeq.eq_of_isGreenH_of_idempotent
      (IsGreenH.trans (IsGreenH.symm (fColoring_isGreenH ctx x))
          (h_val_eq ▸ fColoring_isGreenH ctx y)) (eId_idem ctx x) (eId_idem ctx y)
    let m_class := fun w ↦ Finset.univ.filter (fun z ↦ hOf ctx z = hOf ctx w)
    have hm_ne_x : (m_class x).Nonempty :=
      ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, rfl⟩⟩
    have hm_ne_y : (m_class y).Nonempty :=
      ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ y, rfl⟩⟩
    let mx := Finset.min' (m_class x) hm_ne_x
    let my := Finset.min' (m_class y) hm_ne_y
    have h_same_H : hOf ctx x = hOf ctx y := by
      rw [hOf_eq_class ctx x, hOf_eq_class ctx y, he_eq_ey]
    have h_class_eq : m_class x = m_class y := by simp only [m_class, h_same_H]
    have h_mx_eq_my : mx = my :=
      le_antisymm
        (Finset.min'_le _ _ (h_class_eq ▸ Finset.min'_mem _ hm_ne_y))
        (Finset.min'_le _ _ (h_class_eq.symm ▸ Finset.min'_mem _ hm_ne_x))
    have h_ese_eq_e : eId ctx x * σ.σ x y * eId ctx x = eId ctx x := by
      by_cases h_mx_lt_x : mx < x
      · have h_prop_x := sigma_props ctx x mx h_mx_lt_x
          (Finset.mem_filter.mp (Finset.min'_mem (m_class x) hm_ne_x)).2
        have h_my_lt_y : my < y := h_mx_eq_my ▸ lt_trans h_mx_lt_x hlt
        have h_prop_y := sigma_props ctx y my h_my_lt_y
          (Finset.mem_filter.mp (Finset.min'_mem (m_class y) hm_ne_y)).2
        have h_val_x : (fColoring ctx x).val = σ.σ mx x := by
          have h_def : (fColoring ctx x).val = eId ctx x * σ.σ mx x * eId ctx x := by
            dsimp only [fColoring]
            rw [dif_pos h_mx_lt_x]
          exact h_def.trans h_prop_x.1
        have h_val_y : (fColoring ctx y).val = σ.σ my y := by
          have h_def : (fColoring ctx y).val = eId ctx y * σ.σ my y * eId ctx y := by
            dsimp only [fColoring]
            rw [dif_pos h_my_lt_y]
          exact h_def.trans h_prop_y.1
        have h_sig_mx_y : σ.σ mx x * σ.σ x y = σ.σ mx y := σ.prop mx x y h_mx_lt_x hlt
        have h_sig_my_y : σ.σ my y = σ.σ mx y := h_mx_eq_my ▸ rfl
        have h_sig_mx_x_eq_my_y : σ.σ mx x = σ.σ my y := h_val_x.symm.trans (h_val_eq.trans h_val_y)
        have h_sig_mx_x_mul_xy : σ.σ mx x * σ.σ x y = σ.σ mx x :=
          h_sig_mx_y.trans (h_sig_my_y.symm.trans h_sig_mx_x_eq_my_y.symm)
        have hdvd : IsGreenLeftDvd (eId ctx x) (σ.σ mx x) := h_prop_x.2.left.right
        have h_e_xy : eId ctx x * σ.σ x y = eId ctx x := by
          rcases hdvd with heq | ⟨w, hw⟩
          · exact heq ▸ h_sig_mx_x_mul_xy
          · calc eId ctx x * σ.σ x y = (w * σ.σ mx x) * σ.σ x y := by rw [hw]
              _ = w * (σ.σ mx x * σ.σ x y) := mul_assoc ..
              _ = w * σ.σ mx x := by rw [h_sig_mx_x_mul_xy]
              _ = eId ctx x := hw.symm
        exact h_e_xy.symm ▸ eId_idem ctx x
      · have h_mx_eq_x : mx = x := le_antisymm
          (Finset.min'_le (m_class x) x (Finset.mem_filter.mpr ⟨Finset.mem_univ x, rfl⟩))
          (not_lt.mp h_mx_lt_x)
        have h_my_lt_y : my < y := h_mx_eq_my ▸ h_mx_eq_x ▸ hlt
        have h_prop_y := sigma_props ctx y my h_my_lt_y
          (Finset.mem_filter.mp (Finset.min'_mem (m_class y) hm_ne_y)).2
        have h_val_x : (fColoring ctx x).val = eId ctx x := by
          dsimp only [fColoring]
          rw [dif_neg h_mx_lt_x]
        have h_val_y : (fColoring ctx y).val = σ.σ my y := by
          have h_def : (fColoring ctx y).val = eId ctx y * σ.σ my y * eId ctx y := by
            dsimp only [fColoring]
            rw [dif_pos h_my_lt_y]
          exact h_def.trans h_prop_y.1
        grind
    have h_sig_H : IsGreenH (σ.σ x y) (eId ctx x) := by
      have hn_min_y : ¬ IsMin y :=
        fun h ↦ lt_irrefl x (lt_of_lt_of_le hlt (h (le_of_lt hlt)))
      have hL_y : lOf ctx y = IsGreenL.eqvClass (σ.σ x y) := by
        rw [lOf, dif_neg hn_min_y]
        exact lOf_well_defined ctx y _ x (Classical.choose_spec (not_isMin_iff.mp hn_min_y)) hlt
      have hn_max_x : ¬ IsMax x :=
        fun h ↦ lt_irrefl y (lt_of_le_of_lt (h (le_of_lt hlt)) hlt)
      have hR_x : rOf ctx x = IsGreenR.eqvClass (σ.σ x y) := by
        rw [rOf, dif_neg hn_max_x]
        exact rOf_well_defined ctx x _ y (Classical.choose_spec (not_isMax_iff.mp hn_max_x)) hlt
      have he_L : eId ctx x ∈ IsGreenL.eqvClass (σ.σ x y) := by
        rw [← hL_y]
        exact (h_same_H ▸ eId_mem ctx x).1
      have he_R : eId ctx x ∈ IsGreenR.eqvClass (σ.σ x y) := by
        rw [← hR_x]
        exact (eId_mem ctx x).2
      exact IsGreenH.symm ⟨he_L, he_R⟩
    obtain ⟨hid1, hid2⟩ := MulSeq.mul_eq_self_of_isGreenH_idempotent h_sig_H (eId_idem ctx x)
    grind

end WithNonemptyAlpha
end WithFintypeAlpha
end WithFintypeS
end RegularDClassCase



section SimonSplit

variable {S : Type*} [Semigroup S]

def JUp (a : S) : Set S := { b | GreenJClass.mk a ≤ GreenJClass.mk b }

def LabelingIn {α : Type*} [LinearOrder α]
    (σ : MultiplicativeLabeling S α) (U : Set S) : Prop :=
  ∀ x y : α, x < y → σ.σ x y ∈ U

lemma irregular_d_class_no_three_seq [Finite S] (a : S) {α : Type*} [LinearOrder α]
    (σ : MultiplicativeLabeling S α) (x y z : α)
    (h_img : LabelingIn σ (JUp a))
    (h_xy : x < y) (h_yz : y < z)
    (h_d1 : IsGreenD (σ.σ x y) a)
    (h_d2 : IsGreenD (σ.σ y z) a) :
    IsRegularDClass (IsGreenD.eqvClass a) :=
  have h_xz_le_xy : GreenJClass.mk (σ.σ x z) ≤ GreenJClass.mk (σ.σ x y) :=
    σ.prop x y z h_xy h_yz ▸ IsGreenJRel.mul_right (σ.σ y z) rfl
  have h_xz_le_a : GreenJClass.mk (σ.σ x z) ≤ GreenJClass.mk a :=
    GreenJClass.mk_eq_mk_iff.mpr (isGreenJ_of_isGreenD h_d1) ▸ h_xz_le_xy
  have h_D_xz_a : IsGreenD (σ.σ x y * σ.σ y z) a :=
    (σ.prop x y z h_xy h_yz).symm ▸ isGreenD_of_isGreenJ
      (GreenJClass.mk_eq_mk_iff.mp (le_antisymm h_xz_le_a (h_img x z (lt_trans h_xy h_yz))))
  (isRegularDClass_iff_exists_idempotent (IsGreenD.eqvClass a) ⟨a, rfl⟩).mpr (
    let ⟨e, he_D, he_idem, _⟩ :=
      (mul_mem_isGreenD_eqvClass_properties ⟨a, rfl⟩ _ _ h_d1 h_d2 h_D_xz_a).2
    ⟨e, he_D, he_idem⟩
  )

variable [Fintype S]

open Classical in
noncomputable def nSElement (x : S) : ℕ :=
  let current_cost := nD (IsGreenD.eqvClass x)
  let strictly_above := Finset.univ.filter
    (fun (y : S) => GreenJClass.mk x < GreenJClass.mk y)
  let max_above := strictly_above.attach.sup (fun ⟨y, _hy⟩ => nSElement y)
  current_cost + max_above
termination_by (Finset.univ.filter
  (fun (y : S) => GreenJClass.mk x < GreenJClass.mk y)).card
decreasing_by
  have h_lt : GreenJClass.mk x < GreenJClass.mk y :=
    (Finset.mem_filter.mp _hy).right
  have h_le : Finset.univ.filter (fun (z : S) => GreenJClass.mk y < GreenJClass.mk z) ⊆
              Finset.univ.filter (fun (z : S) => GreenJClass.mk x < GreenJClass.mk z) := by
                grind
  have h_ne : Finset.univ.filter (fun (z : S) => GreenJClass.mk y < GreenJClass.mk z) ≠
              Finset.univ.filter (fun (z : S) => GreenJClass.mk x < GreenJClass.mk z) := by
                grind
  exact Finset.card_lt_card (lt_of_le_of_ne h_le h_ne)

open Classical in
noncomputable def nS (S : Type*) [Semigroup S] [Fintype S] : ℕ :=
  let all_vals := Finset.univ.image (fun (x : S) => nSElement x)
  if h : all_vals.Nonempty then
    Finset.max' all_vals h
  else
    0

lemma nSElement_pos (x : S) : 0 < nSElement x := by
  rw [nSElement]
  have h_pos : 0 < nD (IsGreenD.eqvClass x) := nD_pos (IsGreenD.eqvClass x) ⟨x, rfl⟩
  omega

instance instNonemptyFin_nSElement (x : S) : Nonempty (Fin (nSElement x)) :=
  Fin.pos_iff_nonempty.mp (nSElement_pos x)

open Classical in
noncomputable def buildXSeq (a : S) {α : Type*} [LinearOrder α] [Fintype α]
    (σ : MultiplicativeLabeling S α) (x : α) : List α :=
  let candidates := Finset.univ.filter (fun y => x < y ∧ IsGreenD (σ.σ x y) a)
  if h : candidates.Nonempty then
    let y := Finset.min' candidates h
    x :: buildXSeq a σ y
  else
    [x]
termination_by (Finset.univ.filter (fun z => x < z)).card
decreasing_by
  have h_mem := Finset.min'_mem _ h
  have h_x_lt_y : x < y := (Finset.mem_filter.mp h_mem).2.1
  have h_le : Finset.univ.filter (fun z => y < z) ⊆ Finset.univ.filter (fun z => x < z) := by
    intro z hz
    rw [Finset.mem_filter] at hz ⊢
    exact ⟨hz.1, lt_trans h_x_lt_y hz.2⟩
  have h_ne : Finset.univ.filter (fun z => y < z) ≠ Finset.univ.filter (fun z => x < z) := by
    intro heq
    have hy_mem : y ∈ Finset.univ.filter (fun z => x < z) := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ y, h_x_lt_y⟩
    rw [← heq] at hy_mem
    have : y < y := (Finset.mem_filter.mp hy_mem).2
    exact lt_irrefl y this
  exact Finset.card_lt_card (lt_of_le_of_ne h_le h_ne)

def OpenIntervalType {α : Type*} [LinearOrder α] (X_seq : List α) (i : ℕ) : Type _ :=
  { y : α // ∃ (h1 : i < X_seq.length) (h2 : i + 1 < X_seq.length),
    X_seq.get ⟨i, h1⟩ < y ∧ y < X_seq.get ⟨i + 1, h2⟩ }
  deriving LinearOrder

open Classical in
noncomputable instance instFintypeOpenInterval {α : Type*} [LinearOrder α] [Fintype α]
    (X_seq : List α) (i : ℕ) :
    Fintype (OpenIntervalType X_seq i) := by
  unfold OpenIntervalType
  classical
  infer_instance

open Classical in
noncomputable instance instFintypeSubtypeX {α : Type*} [LinearOrder α] [Fintype α]
    (X_seq : List α) :
    Fintype {x : α // x ∈ X_seq} := by
  classical
  infer_instance

noncomputable def RegularSplits {α S : Type*}
    [LinearOrder α] [Fintype α] [Nonempty α] [Semigroup S] [Fintype S]
    (a : S) (X_seq : List α) [Nonempty {x // x ∈ X_seq}]
    [Nonempty (Fin (nD (IsGreenD.eqvClass a)))]
    (sX : Split {x // x ∈ X_seq} (nD (IsGreenD.eqvClass a)))
    (sY : ∀ (i : ℕ) [Nonempty (OpenIntervalType X_seq i)],
      Split (OpenIntervalType X_seq i) (nSElement a)) :
    Split α (nSElement a) := fun x =>
  if hx : x ∈ X_seq then
    ⟨(sX ⟨x, hx⟩).val + (nSElement a - nD (IsGreenD.eqvClass a)), by
      have := (sX ⟨x, hx⟩).isLt
      rw [nSElement]
      omega⟩
  else if h_ex : ∃ i, ∃ (h1 : i < X_seq.length) (h2 : i + 1 < X_seq.length),
      X_seq.get ⟨i, h1⟩ < x ∧ x < X_seq.get ⟨i + 1, h2⟩ then
    @sY (Classical.choose h_ex) ⟨⟨x, Classical.choose_spec h_ex⟩⟩
      ⟨x, Classical.choose_spec h_ex⟩
  else
    ⟨0, nSElement_pos a⟩

lemma RegularSplits_props {α S : Type*}
    [LinearOrder α] [Fintype α] [Nonempty α] [Semigroup S] [Fintype S]
    (a : S) (X_seq : List α) [Nonempty {x // x ∈ X_seq}]
    [Nonempty (Fin (nD (IsGreenD.eqvClass a)))]
    (σ : MultiplicativeLabeling S α)
    (σ_X : MultiplicativeLabeling S {x // x ∈ X_seq})
    (σ_Y : ∀ (i : ℕ), MultiplicativeLabeling S (OpenIntervalType X_seq i))
    (sX : Split {x // x ∈ X_seq} (nD (IsGreenD.eqvClass a)))
    (sY : ∀ (i : ℕ) [Nonempty (OpenIntervalType X_seq i)],
      Split (OpenIntervalType X_seq i) (nSElement a))
    (_hsX_norm : IsNormalized sX) (hsX_ramsey : IsRamsey σ_X sX)
    (_hsY_norm : ∀ (i : ℕ) [Nonempty (OpenIntervalType X_seq i)], IsNormalized (sY i))
    (hsY_ramsey : ∀ (i : ℕ) [Nonempty (OpenIntervalType X_seq i)], IsRamsey (σ_Y i) (sY i))
    (h_min_in : (Finset.min' (Finset.univ : Finset α) Finset.univ_nonempty) ∈ X_seq)
    (h_σ_X : ∀ x y, σ_X.σ x y = σ.σ x.val y.val)
    (h_σ_Y : ∀ i x y, (σ_Y i).σ x y = σ.σ x.val y.val)
    (h_cov : ∀ x, x ∉ X_seq →
      ∃ (i : ℕ) (h1 : i < X_seq.length) (h2 : i + 1 < X_seq.length),
        X_seq.get ⟨i, h1⟩ < x ∧ x < X_seq.get ⟨i + 1, h2⟩)
    (hsY_strict : ∀ (i : ℕ) [Nonempty (OpenIntervalType X_seq i)]
      (z : OpenIntervalType X_seq i),
      (sY i z).val < nSElement a - nD (IsGreenD.eqvClass a))
    (h_interval_ramsey : ∀ x y, x ∉ X_seq → x < y →
      SplitRelation (RegularSplits a X_seq sX sY) x y →
      ∃ (i : ℕ) (_h_ne : Nonempty (OpenIntervalType X_seq i))
        (x_val y_val : OpenIntervalType X_seq i),
        x_val.val = x ∧ y_val.val = y ∧ SplitRelation (sY i) x_val y_val)
    (h_min_sX : (sX ⟨Finset.min' (Finset.univ : Finset α) Finset.univ_nonempty,
      h_min_in⟩).val = nD (IsGreenD.eqvClass a) - 1)
    (h_max_val : (Finset.max' (Finset.univ : Finset (Fin (nSElement a)))
      Finset.univ_nonempty).val = nSElement a - 1)
    (h_N_pos : 0 < nD (IsGreenD.eqvClass a))
    (h_N_le_M : nD (IsGreenD.eqvClass a) ≤ nSElement a) :
    IsNormalized (RegularSplits a X_seq sX sY) ∧
    IsRamsey σ (RegularSplits a X_seq sX sY) := by
  constructor
  · unfold IsNormalized
    apply Fin.ext
    dsimp [RegularSplits]
    simp only [h_min_in, ↓reduceDIte]
    rw [h_min_sX, h_max_val]
    omega
  · intro x y hlt hsr
    let s := RegularSplits a X_seq sX sY
    have h_eval_not_X : ∀ z, z ∉ X_seq →
        (s z).val < nSElement a - nD (IsGreenD.eqvClass a) := by
      intro z hz
      dsimp [s, RegularSplits]
      split_ifs with h_ex
      · exact @hsY_strict _ ⟨⟨z, Classical.choose_spec h_ex⟩⟩ _
      · obtain ⟨i, h1, h2, hb⟩ := h_cov z hz
        exact False.elim (h_ex ⟨i, h1, h2, hb⟩)
    by_cases hx : x ∈ X_seq
    · have hy : y ∈ X_seq := by
        by_contra hny
        have h1 := h_eval_not_X y hny
        have h3 : (s x).val = (s y).val := congrArg Fin.val hsr.left
        have h_sx : (s x).val = (sX ⟨x, hx⟩).val + (nSElement a - nD (IsGreenD.eqvClass a)) := by
          dsimp [s, RegularSplits]
          simp [hx]
        omega
      have hsr_X : SplitRelation sX ⟨x, hx⟩ ⟨y, hy⟩ := by
        constructor
        · apply Fin.ext
          have eqxy : (s x).val = (s y).val := congrArg Fin.val hsr.left
          have h_sx : (s x).val = (sX ⟨x, hx⟩).val + (nSElement a - nD (IsGreenD.eqvClass a)) := by
            dsimp [s, RegularSplits]
            simp [hx]
          have h_sy : (s y).val = (sX ⟨y, hy⟩).val + (nSElement a - nD (IsGreenD.eqvClass a)) := by
            dsimp [s, RegularSplits]
            simp [hy]
          omega
        · intro z hz1 hz2
          have h_min_eq : min (⟨x, hx⟩ : {x // x ∈ X_seq}) ⟨y, hy⟩ = ⟨x, hx⟩ :=
            min_eq_left (le_of_lt hlt)
          have h_max_eq : max (⟨x, hx⟩ : {x // x ∈ X_seq}) ⟨y, hy⟩ = ⟨y, hy⟩ :=
            max_eq_right (le_of_lt hlt)
          have hz1' : ⟨x, hx⟩ ≤ z := by rwa [h_min_eq] at hz1
          have hz2' : z ≤ ⟨y, hy⟩ := by rwa [h_max_eq] at hz2
          have h_min_alpha : min x y = x := min_eq_left (le_of_lt hlt)
          have h_max_alpha : max x y = y := max_eq_right (le_of_lt hlt)
          have h_le1 : min x y ≤ z.val := by
            rw [h_min_alpha]
            exact hz1'
          have h_le2 : z.val ≤ max x y := by
            rw [h_max_alpha]
            exact hz2'
          have h_sz := hsr.right z.val h_le1 h_le2
          have h_sz_val := Fin.le_iff_val_le_val.mp h_sz
          have hz_eq : (s z.val).val = (sX z).val + (nSElement a - nD (IsGreenD.eqvClass a)) := by
            dsimp [s, RegularSplits]
            simp [z.property]
          have hx_eq :
            (s (min x y)).val = (sX ⟨x, hx⟩).val + (nSElement a - nD (IsGreenD.eqvClass a)) := by
              dsimp [s, RegularSplits]
              rw [h_min_alpha]
              simp [hx]
          rw [hz_eq, hx_eq] at h_sz_val
          apply Fin.le_iff_val_le_val.mpr
          rw [h_min_eq]
          omega
      have h_idem_X := hsX_ramsey ⟨x, hx⟩ ⟨y, hy⟩ hlt hsr_X
      rwa [h_σ_X] at h_idem_X
    · obtain ⟨i, h_ne, x_val, y_val, hx_eq, hy_eq, hsr_Y⟩ :=
        h_interval_ramsey x y hx hlt hsr
      have hlt_Y : x_val < y_val := by
        have h_lt_copy := hlt
        rw [← hx_eq, ← hy_eq] at h_lt_copy
        exact h_lt_copy
      have h_idem_Y := hsY_ramsey i x_val y_val hlt_Y hsr_Y
      rwa [h_σ_Y i x_val y_val, hx_eq, hy_eq] at h_idem_Y

noncomputable def IrregularSplits {α S : Type*}
    [LinearOrder α] [Fintype α] [Nonempty α] [Semigroup S] [Fintype S]
    (a : S) (X_seq : List α)
    (sY : ∀ (i : ℕ) [Nonempty (OpenIntervalType X_seq i)],
      Split (OpenIntervalType X_seq i) (nSElement a)) :
    Split α (nSElement a) := fun x =>
  if hx : x ∈ X_seq then
    ⟨nSElement a - 1, by
      have := nSElement_pos a
      omega
    ⟩
  else if h_ex : ∃ i, ∃ (h1 : i < X_seq.length) (h2 : i + 1 < X_seq.length),
      X_seq.get ⟨i, h1⟩ < x ∧ x < X_seq.get ⟨i + 1, h2⟩ then
    @sY (Classical.choose h_ex) ⟨⟨x, Classical.choose_spec h_ex⟩⟩
      ⟨x, Classical.choose_spec h_ex⟩
  else
    ⟨0, nSElement_pos a⟩

lemma IrregularSplits_props {α S : Type*}
    [LinearOrder α] [Fintype α] [Nonempty α] [Semigroup S] [Fintype S]
    (a : S) (X_seq : List α)
    (σ : MultiplicativeLabeling S α)
    (σ_Y : ∀ (i : ℕ), MultiplicativeLabeling S (OpenIntervalType X_seq i))
    (sY : ∀ (i : ℕ) [Nonempty (OpenIntervalType X_seq i)],
      Split (OpenIntervalType X_seq i) (nSElement a))
    (_hsY_norm : ∀ (i : ℕ) [Nonempty (OpenIntervalType X_seq i)], IsNormalized (sY i))
    (hsY_ramsey : ∀ (i : ℕ) [Nonempty (OpenIntervalType X_seq i)], IsRamsey (σ_Y i) (sY i))
    (h_min_in : (Finset.min' (Finset.univ : Finset α) Finset.univ_nonempty) ∈ X_seq)
    (h_max_val : (Finset.max' (Finset.univ : Finset (Fin (nSElement a)))
      Finset.univ_nonempty).val = nSElement a - 1)
    (h_σ_Y : ∀ i x y, (σ_Y i).σ x y = σ.σ x.val y.val)
    (h_cov : ∀ x, x ∉ X_seq →
      ∃ (i : ℕ) (h1 : i < X_seq.length) (h2 : i + 1 < X_seq.length),
        X_seq.get ⟨i, h1⟩ < x ∧ x < X_seq.get ⟨i + 1, h2⟩)
    (hsY_strict : ∀ (i : ℕ) [Nonempty (OpenIntervalType X_seq i)],
      ∀ z : OpenIntervalType X_seq i, (sY i z).val < nSElement a - 1)
    (h_interval_ramsey : ∀ x y, x ∉ X_seq → x < y →
      SplitRelation (IrregularSplits a X_seq sY) x y →
      ∃ (i : ℕ) (_h_ne : Nonempty (OpenIntervalType X_seq i))
        (x_val y_val : OpenIntervalType X_seq i),
        x_val.val = x ∧ y_val.val = y ∧ SplitRelation (sY i) x_val y_val)
    (h_X_ramsey : ∀ x y, x ∈ X_seq → y ∈ X_seq → x < y →
      SplitRelation (IrregularSplits a X_seq sY) x y →
      σ.σ x y * σ.σ x y = σ.σ x y) :
    IsNormalized (IrregularSplits a X_seq sY) ∧
    IsRamsey σ (IrregularSplits a X_seq sY) := by
  constructor
  · unfold IsNormalized
    apply Fin.ext
    simp [IrregularSplits, h_min_in, h_max_val]
  · intro x y hlt hsr
    let s := IrregularSplits a X_seq sY
    have h_eval_not_X : ∀ z, z ∉ X_seq → (s z).val < nSElement a - 1 := by
      intro z hz
      dsimp [s, IrregularSplits]
      split_ifs with h_ex
      · exact @hsY_strict (Classical.choose h_ex)
          ⟨⟨z, Classical.choose_spec h_ex⟩⟩ ⟨z, Classical.choose_spec h_ex⟩
      · obtain ⟨i, h1, h2, hb⟩ := h_cov z hz
        exact False.elim (h_ex ⟨i, h1, h2, hb⟩)
    by_cases hx : x ∈ X_seq
    · have hy : y ∈ X_seq := by
        by_contra hny
        have h1 := h_eval_not_X y hny
        have h3 : (s x).val = (s y).val := congrArg Fin.val hsr.left
        have h_sx : (s x).val = nSElement a - 1 := by
          dsimp [s, IrregularSplits]
          simp [hx]
        omega
      exact h_X_ramsey x y hx hy hlt hsr
    · obtain ⟨i, h_ne, x_val, y_val, hx_eq, hy_eq, hsr_Y⟩ :=
        h_interval_ramsey x y hx hlt hsr
      have hlt_Y : x_val < y_val := by
        have h_lt_copy := hlt
        rw [← hx_eq, ← hy_eq] at h_lt_copy
        exact h_lt_copy
      have h_idem_Y := @hsY_ramsey i h_ne x_val y_val hlt_Y hsr_Y
      rwa [h_σ_Y i x_val y_val, hx_eq, hy_eq] at h_idem_Y

lemma simon_split_induction_aux {S : Type*} [Semigroup S] [Fintype S]
    (n : ℕ) :
    ∀ (a : S) (hn : nSElement a ≤ n)
    {α : Type*} [LinearOrder α] [Fintype α] [Nonempty α]
    (σ : MultiplicativeLabeling S α)
    (h_img : LabelingIn σ (JUp a)),
    ∃ (s : Split α (nSElement a)), IsNormalized s ∧ IsRamsey σ s := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro a hn α instLin instFin instNon σ h_img
    let x_0 := Finset.min' (Finset.univ : Finset α) Finset.univ_nonempty
    let X_seq := buildXSeq a σ x_0
    have h_X_ne : X_seq ≠ [] := by
      intro h_eq
      unfold X_seq at h_eq
      rw [buildXSeq] at h_eq
      dsimp only at h_eq
      split at h_eq
      · contradiction
      · contradiction
    haveI instX : Nonempty { x // x ∈ X_seq } := by
      cases h : X_seq
      · exact False.elim (h_X_ne h)
      · next hd tl => exact ⟨⟨hd, by simp⟩⟩
    let σ_X : MultiplicativeLabeling S { x // x ∈ X_seq } :=
      ⟨fun x y ↦ σ.σ x y, fun x y z hxy hyz ↦ σ.prop x y z hxy hyz⟩
    let Y_α (i : Nat) := OpenIntervalType X_seq i
    let σ_Y (i : Nat) : MultiplicativeLabeling S (Y_α i) :=
      ⟨fun y z ↦ σ.σ y.1 z.1, fun y z w hyz hzw ↦ σ.prop y.1 z.1 w.1 hyz hzw⟩
    have h_min_in : x_0 ∈ X_seq := by
      change x_0 ∈ buildXSeq a σ x_0
      rw [buildXSeq]
      split
      · simp
      · simp
    have h_min_in_alpha : (Finset.min' Finset.univ (Finset.univ_nonempty (α := α))) ∈ X_seq :=
      h_min_in
    have h_σ_X_eq : ∀ x y, σ_X.σ x y = σ.σ x.val y.val := fun _ _ ↦ rfl
    have h_σ_Y_eq : ∀ i x y, (σ_Y i).σ x y = σ.σ x.val y.val := fun _ _ _ ↦ rfl
    by_cases h_reg : IsRegularDClass (IsGreenD.eqvClass a)
    · have h_nD_pos : 0 < nD (IsGreenD.eqvClass a) :=
        nD_pos (IsGreenD.eqvClass a) ⟨a, rfl⟩
      haveI instFinFin : Nonempty (Fin (nD (IsGreenD.eqvClass a))) := ⟨⟨0, h_nD_pos⟩⟩
      have h_X_split : ∃ sX : Split {x // x ∈ X_seq} (nD (IsGreenD.eqvClass a)),
          IsNormalized sX ∧ IsRamsey σ_X sX := by
        have h_range : ∀ (x y : {x // x ∈ X_seq}), x < y → σ_X.σ x y ∈ IsGreenD.eqvClass a := by
          sorry
        exact simon_regular_d_case σ_X (IsGreenD.eqvClass a) ⟨a, rfl⟩ h_reg h_range
      have h_Y_strict : ∀ (i : Nat) [h : Nonempty (Y_α i)],
          LabelingIn (σ_Y i) {b | GreenJClass.mk a < GreenJClass.mk b} := by
        intro i h_ne x y h_lt
        sorry
      have h_Y_splits : ∀ (i : Nat) [h : Nonempty (Y_α i)],
          ∃ (sY : Split (Y_α i) (nSElement a)),
          IsNormalized sY ∧ IsRamsey (σ_Y i) sY := by
        intro i h_ne
        have h_b_exists : ∃ (b : S), LabelingIn (σ_Y i) (JUp b) ∧ nSElement b < nSElement a := by
          sorry
        obtain ⟨b, hb_img, hb_lt⟩ := h_b_exists
        have hb_le_n : nSElement b ≤ n - 1 := by omega
        obtain ⟨sY_b, hsY_norm, hsY_ramsey⟩ := ih (n - 1) (by omega) b hb_le_n (σ_Y i) hb_img
        let embed_fin (v : Fin (nSElement b)) : Fin (nSElement a) :=
          ⟨v.val, by
            have := v.isLt
            omega
          ⟩
        use fun y ↦ embed_fin (sY_b y)
        constructor
        · sorry
        · sorry
      obtain ⟨sX, hsX_norm, hsX_ramsey⟩ := h_X_split
      let sY_fun (i : Nat) [h : Nonempty (Y_α i)] := Classical.choose (h_Y_splits i)
      have hsY_norm : ∀ (i : Nat) [h : Nonempty (Y_α i)], IsNormalized (sY_fun i) := by
        intro i h
        exact (Classical.choose_spec (h_Y_splits i)).1
      have hsY_ramsey : ∀ (i : Nat) [h : Nonempty (Y_α i)], IsRamsey (σ_Y i) (sY_fun i) := by
        intro i h
        exact (Classical.choose_spec (h_Y_splits i)).2
      let s := RegularSplits a X_seq sX sY_fun
      use s
      have h_cov : ∀ x ∉ X_seq, ∃ i h1 h2, X_seq.get ⟨i, h1⟩ < x ∧ x < X_seq.get ⟨i + 1, h2⟩ :=
        sorry
      have hsY_strict : ∀ (i : ℕ) [inst : Nonempty (Y_α i)] (z : Y_α i),
          (sY_fun i z).val < nSElement a - nD (IsGreenD.eqvClass a) := sorry
      have h_interval_ramsey : ∀ x y, x ∉ X_seq → x < y → SplitRelation s x y →
        ∃ (i : ℕ) (h_ne : Nonempty (Y_α i)) (xv yv : Y_α i),
          xv.val = x ∧ yv.val = y ∧ SplitRelation (@sY_fun i h_ne) xv yv := sorry
      have h_min_sX :
        (sX ⟨Finset.min' _ Finset.univ_nonempty, h_min_in⟩).val =
          nD (IsGreenD.eqvClass a) - 1 := sorry
      have h_max_val : (Finset.max' (Finset.univ : Finset (Fin (nSElement a)))
        Finset.univ_nonempty).val = nSElement a - 1 := sorry
      have h_N_pos : 0 < nD (IsGreenD.eqvClass a) := nD_pos (IsGreenD.eqvClass a) ⟨a, rfl⟩
      have h_N_le_M : nD (IsGreenD.eqvClass a) ≤ nSElement a := sorry
      constructor
      · exact (RegularSplits_props a X_seq σ σ_X σ_Y sX sY_fun hsX_norm hsX_ramsey
          hsY_norm hsY_ramsey h_min_in_alpha h_σ_X_eq h_σ_Y_eq h_cov hsY_strict
            h_interval_ramsey h_min_sX h_max_val h_N_pos h_N_le_M).1
      · exact (RegularSplits_props a X_seq σ σ_X σ_Y sX sY_fun hsX_norm hsX_ramsey
          hsY_norm hsY_ramsey h_min_in_alpha h_σ_X_eq h_σ_Y_eq h_cov hsY_strict
            h_interval_ramsey h_min_sX h_max_val h_N_pos h_N_le_M).2
    · have h_Y_strict : ∀ (i : Nat) [h : Nonempty (Y_α i)],
          LabelingIn (σ_Y i) {b | GreenJClass.mk a < GreenJClass.mk b} := by
        intro i h_ne x y h_lt
        sorry
      have h_Y_splits : ∀ (i : Nat) [h : Nonempty (Y_α i)],
          ∃ (sY : Split (Y_α i) (nSElement a)),
          IsNormalized sY ∧ IsRamsey (σ_Y i) sY := by
        intro i h_ne
        have h_b_exists : ∃ (b : S), LabelingIn (σ_Y i) (JUp b) ∧ nSElement b < nSElement a := by
          sorry
        obtain ⟨b, hb_img, hb_lt⟩ := h_b_exists
        have hb_le_n : nSElement b ≤ n - 1 := by omega
        obtain ⟨sY_b, hsY_norm, hsY_ramsey⟩ := ih (n - 1) (by omega) b hb_le_n (σ_Y i) hb_img
        let embed_fin (v : Fin (nSElement b)) : Fin (nSElement a) :=
          ⟨v.val, by
            have := v.isLt
            omega
          ⟩
        use fun y ↦ embed_fin (sY_b y)
        constructor
        · sorry
        · sorry
      let sY_fun (i : Nat) [h : Nonempty (Y_α i)] := Classical.choose (h_Y_splits i)
      have hsY_norm : ∀ (i : Nat) [h : Nonempty (Y_α i)], IsNormalized (sY_fun i) := by
        intro i h
        exact (Classical.choose_spec (h_Y_splits i)).1
      have hsY_ramsey : ∀ (i : Nat) [h : Nonempty (Y_α i)], IsRamsey (σ_Y i) (sY_fun i) := by
        intro i h
        exact (Classical.choose_spec (h_Y_splits i)).2
      let s := IrregularSplits a X_seq sY_fun
      use s
      have h_cov : ∀ x ∉ X_seq, ∃ i h1 h2, X_seq.get ⟨i, h1⟩ < x ∧ x < X_seq.get ⟨i + 1, h2⟩ :=
        sorry
      have hsY_strict : ∀ (i : ℕ) [inst : Nonempty (Y_α i)] (z : Y_α i),
          (sY_fun i z).val < nSElement a - 1 := sorry
      have h_interval_ramsey : ∀ x y, x ∉ X_seq → x < y → SplitRelation s x y →
        ∃ (i : ℕ) (h_ne : Nonempty (Y_α i)) (xv yv : Y_α i),
          xv.val = x ∧ yv.val = y ∧ SplitRelation (@sY_fun i h_ne) xv yv := sorry
      have h_max_val : (Finset.max' (Finset.univ : Finset (Fin (nSElement a)))
        Finset.univ_nonempty).val = nSElement a - 1 := sorry
      have h_X_ramsey : ∀ x y, x ∈ X_seq → y ∈ X_seq → x < y → SplitRelation s x y →
          σ.σ x y * σ.σ x y = σ.σ x y := sorry
      constructor
      · exact (IrregularSplits_props a X_seq σ σ_Y sY_fun hsY_norm hsY_ramsey
          h_min_in_alpha h_max_val h_σ_Y_eq h_cov hsY_strict
            h_interval_ramsey h_X_ramsey).1
      · exact (IrregularSplits_props a X_seq σ σ_Y sY_fun hsY_norm hsY_ramsey
          h_min_in_alpha h_max_val h_σ_Y_eq h_cov hsY_strict
            h_interval_ramsey h_X_ramsey).2

lemma simon_split_induction (a : S) {α : Type*} [LinearOrder α] [Fintype α] [Nonempty α]
    (σ : MultiplicativeLabeling S α)
    (h_img : LabelingIn σ (JUp a)) :
    ∃ (s : Split α (nSElement a)), IsNormalized s ∧ IsRamsey σ s :=
  simon_split_induction_aux (nSElement a) a le_rfl σ h_img

theorem simon_split {S α : Type*} [Semigroup S] [Fintype S]
    [LinearOrder α] [Fintype α] [Nonempty α] [Nonempty (Fin (nS S))]
    (σ : MultiplicativeLabeling S α) :
    ∃ (s : Split α (nS S)), IsNormalized s ∧ IsRamsey σ s := by
  let x_0 := Finset.min' (Finset.univ : Finset α) Finset.univ_nonempty
  let y_0 := Finset.max' (Finset.univ : Finset α) Finset.univ_nonempty
  let a := σ.σ x_0 y_0
  have ha : LabelingIn σ (JUp a) := by
    intros x y hlt
    have hx0 : x_0 ≤ x := Finset.min'_le _ _ (Finset.mem_univ _)
    have hy0 : y ≤ y_0 := Finset.le_max' _ _ (Finset.mem_univ _)
    change IsGreenJRel (σ.σ x_0 y_0) (σ.σ x y)
    rcases hx0.eq_or_lt with rfl | hx0_lt
    · rcases hy0.eq_or_lt with rfl | hy0_lt
      · exact IsGreenJRel.eq rfl
      · have h_prop := σ.prop _ y y_0 hlt hy0_lt
        exact IsGreenJRel.mul_right (σ.σ y y_0) h_prop.symm
    · rcases hy0.eq_or_lt with rfl | hy0_lt
      · have h_prop := σ.prop x_0 x _ hx0_lt hlt
        exact IsGreenJRel.mul_left (σ.σ x_0 x) h_prop.symm
      · have h1 := σ.prop x_0 x y hx0_lt hlt
        have h2 := σ.prop x_0 y y_0 (lt_trans hx0_lt hlt) hy0_lt
        exact IsGreenJRel.mul_both (σ.σ x_0 x) (σ.σ y y_0) (by rw [← h2, ← h1])
  obtain ⟨s_a, h_norm, h_ramsey⟩ := simon_split_induction a σ ha
  have h_le : nSElement a ≤ nS S := by
    unfold nS
    have h_nonempty : (Finset.univ.image (fun (x : S) => nSElement x)).Nonempty :=
      ⟨nSElement a, Finset.mem_image_of_mem _ (Finset.mem_univ a)⟩
    rw [dif_pos h_nonempty]
    exact Finset.le_max' _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ a))
  let Δ := nS S - nSElement a
  have h_bound : ∀ x, (s_a x).val + Δ < nS S := by
    intro x
    have := (s_a x).isLt
    omega
  let s : Split α (nS S) := fun x => ⟨(s_a x).val + Δ, h_bound x⟩
  use s
  constructor
  · unfold IsNormalized at h_norm ⊢
    ext
    have h_val2 := congrArg Fin.val h_norm
    have h_pos : 0 < nSElement a := nSElement_pos a
    have h_nS_pos : 0 < nS S := Fin.pos_iff_nonempty.mpr
      (inferInstance : Nonempty (Fin (nS S)))
    have h_max_a : (Finset.max' (Finset.univ : Finset (Fin (nSElement a)))
      Finset.univ_nonempty).val = nSElement a - 1 := by
      have hm : Finset.max' (Finset.univ : Finset (Fin (nSElement a)))
        Finset.univ_nonempty = ⟨nSElement a - 1, by omega⟩ := by
        rw [Finset.max'_eq_iff]
        exact ⟨Finset.mem_univ _, fun w _ =>
          Fin.le_iff_val_le_val.mpr (by simp; have := w.isLt; omega)⟩
      rw [hm]
    have h_max_S : (Finset.max' (Finset.univ : Finset (Fin (nS S)))
      Finset.univ_nonempty).val = nS S - 1 := by
      have hm : Finset.max' (Finset.univ : Finset (Fin (nS S))) Finset.univ_nonempty =
        ⟨nS S - 1, by omega⟩ := by
        rw [Finset.max'_eq_iff]
        exact ⟨Finset.mem_univ _, fun w _ =>
          Fin.le_iff_val_le_val.mpr (by simp; have := w.isLt; omega)⟩
      rw [hm]
    have h_s_def : (s (Finset.min' Finset.univ Finset.univ_nonempty)).val =
      (s_a (Finset.min' Finset.univ Finset.univ_nonempty)).val + Δ := rfl
    rw [h_s_def, h_max_S]
    omega
  · unfold IsRamsey
    intros x y hlt hsr
    apply h_ramsey x y hlt
    unfold SplitRelation at hsr ⊢
    constructor
    · have h_eq := hsr.left
      have h_val : (s_a x).val + Δ = (s_a y).val + Δ := congrArg Fin.val h_eq
      ext
      omega
    · intros z hz1 hz2
      have h_le_fin := hsr.right z hz1 hz2
      have h_le_val : (s_a z).val + Δ ≤ (s_a (min x y)).val + Δ := Fin.le_iff_val_le_val.mp h_le_fin
      apply Fin.le_iff_val_le_val.mpr
      omega

end SimonSplit



section SplitToTree

inductive FactorizationTree (A : Type*)
| leaf (a : A)
| binary (left right : FactorizationTree A)
| nary (children : List (FactorizationTree A))

def FactorizationTree.height {A : Type*} : FactorizationTree A → ℕ
| leaf _ => 0
| binary l r => max l.height r.height + 1
| nary cs => cs.foldl (fun acc c => max acc c.height) 0 + 1

def FactorizationTree.word {A : Type*} : FactorizationTree A → List A
| leaf a => [a]
| binary l r => l.word ++ r.word
| nary cs => cs.flatMap FactorizationTree.word

def IsRamseyTree {A S : Type*} [Semigroup S] (eval : List A → S) :
    FactorizationTree A → Prop
| FactorizationTree.leaf _ => True
| FactorizationTree.binary l r => IsRamseyTree eval l ∧ IsRamseyTree eval r
| FactorizationTree.nary cs =>
    cs.length ≥ 3 ∧
    (∀ c ∈ cs, IsRamseyTree eval c) ∧
    ∃ (e : S), e * e = e ∧ (∀ c ∈ cs, eval c.word = e)

def wordLabeling {A S : Type*} [Semigroup S]
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (u : List A) : MultiplicativeLabeling S (Fin (u.length + 1)) where
  σ := fun i j => eval ((u.drop i.val).take (j.val - i.val))
  prop := by
    intros x y z hxy hyz
    let u_xy := (u.drop x.val).take (y.val - x.val)
    let u_yz := (u.drop y.val).take (z.val - y.val)
    let u_xz := (u.drop x.val).take (z.val - x.val)
    have h1 : u_xy ≠ [] ∧ u_yz ≠ [] := by
      simp [u_xy, u_yz]
      omega
    have h2 : u_xy ++ u_yz = u_xz := by
      have h_add : z.val - x.val = (y.val - x.val) + (z.val - y.val) := by
        omega
      have h_drop : u.drop y.val = (u.drop x.val).drop (y.val - x.val) := by
        simp
        grind
      grind
    grind

lemma exists_factorizationTree_of_split {A S : Type*} [Semigroup S]
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (u : List A) (hu : u ≠ [])
    {k : ℕ} [Nonempty (Fin k)]
    (s : Split (Fin (u.length + 1)) k)
    (hs_norm : IsNormalized s)
    (hs_ramsey : IsRamsey (wordLabeling eval hmul u) s) :
    ∃ (t : FactorizationTree A), t.word = u ∧
      t.height ≤ 3 * k - 1 ∧ IsRamseyTree eval t := by
  sorry

end SplitToTree



section FactorizationForest

theorem factorization_forest {A S : Type*} [Semigroup S] [Fintype S]
    [Nonempty (Fin (nS S))]
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (u : List A) (hu : u ≠ []) :
    ∃ (t : FactorizationTree A), t.word = u ∧
      t.height ≤ 3 * (nS S) - 1 ∧ IsRamseyTree eval t := by
  sorry

end FactorizationForest
