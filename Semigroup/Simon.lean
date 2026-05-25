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
  let sizeG := Fintype.card G
  let x₀ : α := Finset.min' .univ Finset.univ_nonempty
  have h_pos : 0 < sizeG := Fintype.card_pos
  have h_size_cast : sizeG - 1 + 1 = sizeG := by omega
  haveI : Nonempty (Fin sizeG) := Fin.pos_iff_nonempty.mp h_pos
  let maxRank : Fin sizeG := Fin.cast h_size_cast (Fin.last (sizeG - 1))
  let rawEquiv := Fintype.equivFin G
  let indexInEnum := rawEquiv.trans (Equiv.swap (rawEquiv 1) maxRank)
  let s : Split α sizeG := fun y ↦
    if y = x₀ then maxRank else indexInEnum (σ.σ x₀ y)
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
      simp only [maxRank]
      exact Nat.le_pred_of_lt hy.is_lt
  · intros x y hlt hsr
    unfold SplitRelation at hsr
    by_cases hx : x = x₀
    · subst hx
      have h_val : σ.σ x₀ y = 1 := Equiv.injective indexInEnum
        (by simpa [s, ne_of_gt hlt, indexInEnum] using hsr.left.symm)
      simp [h_val]
    · have h_lt : x₀ < x := (Finset.min'_le _ x (Finset.mem_univ x)).lt_of_ne (Ne.symm hx)
      have h_eq : σ.σ x₀ x = σ.σ x₀ y := Equiv.injective indexInEnum
        (by simpa [s, hx, ne_of_gt (lt_trans h_lt hlt)] using hsr.left)
      have h_one : σ.σ x y = 1 := by simpa [h_eq] using σ.prop x₀ x y h_lt hlt
      simp [h_one]

end GroupCase



section HClassGroupCase

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
      (∀ x y : X, x < y → SplitRelation s x y →
        σ.σ x y * σ.σ x y = σ.σ x y) := by
  classical
  let σHFun : X → X → H := fun x y ↦
    if h : x < y then ⟨σ.σ x y, h_range x y x.2 y.2 h⟩ else 1
  have σH_prop : ∀ (x y z : X), x < y → y < z → σHFun x y * σHFun y z = σHFun x z := by
    intro x y z hxy hyz
    ext
    dsimp [σHFun]
    rw [dif_pos hxy, dif_pos hyz, dif_pos (lt_trans hxy hyz)]
    rw [← h_mul_eq]
    exact σ.prop x y z hxy hyz
  let σH : MultiplicativeLabeling H X := ⟨σHFun, σH_prop⟩
  obtain ⟨sH, h_norm, h_ramsey⟩ := simon_group_case σH
  use sH; constructor
  · exact h_norm
  · intro x y hxy h_split
    have h_eq := congr_arg Subtype.val (h_ramsey x y hxy h_split)
    rw [← h_mul_eq] at h_eq
    dsimp [σH, σHFun] at h_eq
    rw [dif_pos hxy] at h_eq
    exact h_eq

end HClassGroupCase



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

/-- The chosen L-class is well-defined and depends only on
  the elements strictly smaller than `x`. -/
lemma lOf_well_defined (ctx : SimonContext S α) (x y1 y2 : α)
    (hy1 : y1 < x) (hy2 : y2 < x) :
    IsGreenL.eqvClass (ctx.σ.σ y1 x) = IsGreenL.eqvClass (ctx.σ.σ y2 x) := by
  wlog h_le : y1 ≤ y2 generalizing y1 y2 hy1 hy2
  · exact (this y2 y1 hy2 hy1 (le_of_lt (not_le.mp h_le))).symm
  · rcases h_le.eq_or_lt with rfl | h_lt
    · rfl
    · have h_prod : ctx.σ.σ y1 x = ctx.σ.σ y1 y2 * ctx.σ.σ y2 x :=
        (ctx.σ.prop y1 y2 x h_lt hy2).symm
      have h_lem := mul_mem_isGreenD_eqvClass_properties ⟨ctx.x₀, ctx.hx₀⟩ _ _
        (ctx.h_range y1 y2 h_lt) (ctx.h_range y2 x hy2) (h_prod ▸ ctx.h_range y1 x hy1)
      have hL : IsGreenL (ctx.σ.σ y2 x) (ctx.σ.σ y1 x) := h_prod ▸ h_lem.1.2
      ext z
      exact ⟨fun hz ↦ IsGreenL.trans hz (IsGreenL.symm hL), fun hz ↦ IsGreenL.trans hz hL⟩

/-- The chosen R-class is well-defined and depends only on
  the elements strictly greater than `x`. -/
lemma rOf_well_defined (ctx : SimonContext S α) (x y1 y2 : α)
    (hy1 : x < y1) (hy2 : x < y2) :
    IsGreenR.eqvClass (ctx.σ.σ x y1) = IsGreenR.eqvClass (ctx.σ.σ x y2) := by
  wlog h_le : y1 ≤ y2 generalizing y1 y2 hy1 hy2
  · exact (this y2 y1 hy2 hy1 (le_of_lt (not_le.mp h_le))).symm
  · rcases h_le.eq_or_lt with rfl | h_lt
    · rfl
    · have h_prod : ctx.σ.σ x y1 * ctx.σ.σ y1 y2 = ctx.σ.σ x y2 := ctx.σ.prop x y1 y2 hy1 h_lt
      have h_lem := mul_mem_isGreenD_eqvClass_properties ⟨ctx.x₀, ctx.hx₀⟩ _ _
        (ctx.h_range x y1 hy1) (ctx.h_range y1 y2 h_lt) (h_prod.symm ▸ ctx.h_range x y2 hy2)
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
    · have h_ex := MulSeq.exists_idempotent_in_greenL_of_regular
        (ctx.hReg ctx.x₀ (ctx.hx₀ ▸ IsGreenD.refl ctx.x₀))
      use choose h_ex
      simp [lOf, rOf, h_min, h_max, choose_spec h_ex, IsGreenR.eqvClass, IsGreenR.refl]
    · have h_ex := MulSeq.exists_idempotent_in_greenR_of_regular (ctx.hReg _ (ctx.h_range x _
        (choose_spec (not_isMax_iff.mp h_max))))
      use choose h_ex
      simp [lOf, rOf, h_min, h_max, choose_spec h_ex, IsGreenL.eqvClass, IsGreenL.refl]
  · by_cases h_max : IsMax x
    · have h_ex := MulSeq.exists_idempotent_in_greenL_of_regular (ctx.hReg _ (ctx.h_range _ x
        (choose_spec (not_isMin_iff.mp h_min))))
      use choose h_ex
      simp [lOf, rOf, h_min, h_max, choose_spec h_ex, IsGreenR.eqvClass, IsGreenR.refl]
    · have h_prod : ctx.σ.σ (choose (not_isMin_iff.mp h_min)) x * ctx.σ.σ x
        (choose (not_isMax_iff.mp h_max)) = ctx.σ.σ (choose (not_isMin_iff.mp h_min))
          (choose (not_isMax_iff.mp h_max)) :=
            ctx.σ.prop _ _ _ (choose_spec (not_isMin_iff.mp h_min))
              (choose_spec (not_isMax_iff.mp h_max))
      obtain ⟨_, ⟨ex, _, he_idem, hLe, hRe⟩⟩ :=
        mul_mem_isGreenD_eqvClass_properties ⟨ctx.x₀, ctx.hx₀⟩ _ _
          (ctx.h_range _ _ (choose_spec (not_isMin_iff.mp h_min)))
          (ctx.h_range _ _ (choose_spec (not_isMax_iff.mp h_max)))
          (h_prod.symm ▸ ctx.h_range _ _ (lt_trans (choose_spec (not_isMin_iff.mp h_min))
            (choose_spec (not_isMax_iff.mp h_max))))
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
      fun ⟨hwL, hwR⟩ =>
        ⟨IsGreenL.trans hwL (IsGreenL.symm he.1), IsGreenR.trans hwR (IsGreenR.symm he.2)⟩,
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
    have h_ex_mem : eId ctx x ∈ lOf ctx x := (eId_mem ctx x).1
    rwa [h_L_mx] at h_ex_mem
  have h_not_max_m : ¬ IsMax m := fun h ↦ lt_irrefl x (lt_of_le_of_lt (h (le_of_lt h_mx)) h_mx)
  have h_R_m : rOf ctx m = IsGreenR.eqvClass (ctx.σ.σ m x) := by
    dsimp only [rOf]
    rw [dif_neg h_not_max_m]
    exact rOf_well_defined ctx m _ x (choose_spec (not_isMax_iff.mp h_not_max_m)) h_mx
  have he_R_sig : IsGreenR (eId ctx x) (ctx.σ.σ m x) := by
    have hx_in_H : eId ctx x ∈ hOf ctx m := hm_H ▸ eId_mem ctx x
    have h_emem : eId ctx x ∈ rOf ctx m := hx_in_H.2
    rwa [h_R_m] at h_emem
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
    have h_step := h_group (eId ctx x) (ctx.σ.σ m x) he_He h_sig_He
    exact h_group (eId ctx x * ctx.σ.σ m x) (eId ctx x) h_step he_He
  have h_val_H_e : IsGreenH val (eId ctx x) := h_val_He
  have hval_D_e : IsGreenD val (eId ctx x) := ⟨val, IsGreenL.refl val, h_val_H_e.right⟩
  have h_val_D : val ∈ ctx.D := by
    rw [ctx.hx₀]
    have h_eId_D : eId ctx x ∈ IsGreenD.eqvClass ctx.x₀ := ctx.hx₀ ▸ eId_mem_D ctx x
    exact IsGreenD.trans hval_D_e h_eId_D
  exact ⟨h_val_D, eId ctx x, eId_mem_D ctx x, eId_idem ctx x, h_val_H_e⟩

section WithFintypeAlpha
variable [Fintype α]

open Classical in
/-- The coloring function mapping an element `x` to a subtype representing
  its value and properties in the D-class. -/
noncomputable def fColoring (ctx : SimonContext S α) (x : α) :
    { y : S // y ∈ ctx.D ∧ ∃ e ∈ ctx.D, e * e = e ∧ IsGreenH y e } :=
  let mClass := Finset.univ.filter (fun y ↦ hOf ctx y = hOf ctx x)
  have hm_nonempty : mClass.Nonempty := ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, rfl⟩⟩
  let m := Finset.min' mClass hm_nonempty
  if h_mx : m < x then
    have hm_H : hOf ctx m = hOf ctx x :=
      (Finset.mem_filter.mp (Finset.min'_mem mClass hm_nonempty)).2
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
  let mClass := Finset.univ.filter (fun w ↦ hOf ctx w = hOf ctx z)
  have hm_nonempty : mClass.Nonempty := ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ z, rfl⟩⟩
  let mz := Finset.min' mClass hm_nonempty
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
  let maxRank : Fin (nD D) := Fin.cast h_card_G_D (Fin.cast (Nat.sub_add_cancel
      (by
        rw [h_card_G_D]
        exact Fin.pos_iff_nonempty.mpr h_ne)) (Fin.last _)
      )
  let indexMap := equiv.trans (Equiv.swap (equiv (fColoring ctx
      (Finset.min' Finset.univ Finset.univ_nonempty))) maxRank)
  use fun y ↦ indexMap (fColoring ctx y)
  constructor
  · change indexMap _ = Finset.max' _ _
    rw [show indexMap _ = maxRank by
      dsimp [indexMap]
      rw [Equiv.trans_apply, Equiv.swap_apply_left]]
    symm
    rw [Finset.max'_eq_iff]
    exact ⟨Finset.mem_univ _, fun y _ ↦ Fin.le_iff_val_le_val.mpr <| by
      have : (maxRank : ℕ) = nD D - 1 := by simp [maxRank, h_card_G_D]
      omega⟩
  · intros x y hlt hsr
    unfold SplitRelation at hsr
    have h_val_eq : (fColoring ctx x).val = (fColoring ctx y).val :=
      congrArg Subtype.val (Equiv.injective indexMap hsr.left)
    have he_eq_ey : eId ctx x = eId ctx y := MulSeq.eq_of_isGreenH_of_idempotent
      (IsGreenH.trans (IsGreenH.symm (fColoring_isGreenH ctx x))
          (h_val_eq ▸ fColoring_isGreenH ctx y)) (eId_idem ctx x) (eId_idem ctx y)
    let mClass := fun w ↦ Finset.univ.filter (fun z ↦ hOf ctx z = hOf ctx w)
    have hm_ne_x : (mClass x).Nonempty := ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, rfl⟩⟩
    have hm_ne_y : (mClass y).Nonempty := ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ y, rfl⟩⟩
    let mx := Finset.min' (mClass x) hm_ne_x
    let my := Finset.min' (mClass y) hm_ne_y
    have h_same_H : hOf ctx x = hOf ctx y := by
      rw [hOf_eq_class ctx x, hOf_eq_class ctx y, he_eq_ey]
    have h_class_eq : mClass x = mClass y := by simp only [mClass, h_same_H]
    have h_mx_eq_my : mx = my :=
      le_antisymm
        (Finset.min'_le _ _ (h_class_eq ▸ Finset.min'_mem _ hm_ne_y))
        (Finset.min'_le _ _ (h_class_eq.symm ▸ Finset.min'_mem _ hm_ne_x))
    have h_ese_eq_e : eId ctx x * σ.σ x y * eId ctx x = eId ctx x := by
      by_cases h_mx_lt_x : mx < x
      · have h_prop_x := sigma_props ctx x mx h_mx_lt_x
          (Finset.mem_filter.mp (Finset.min'_mem (mClass x) hm_ne_x)).2
        have h_my_lt_y : my < y := h_mx_eq_my ▸ lt_trans h_mx_lt_x hlt
        have h_prop_y := sigma_props ctx y my h_my_lt_y
          (Finset.mem_filter.mp (Finset.min'_mem (mClass y) hm_ne_y)).2
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
          (Finset.min'_le (mClass x) x (Finset.mem_filter.mpr ⟨Finset.mem_univ x, rfl⟩))
          (not_lt.mp h_mx_lt_x)
        have h_my_lt_y : my < y := h_mx_eq_my ▸ h_mx_eq_x ▸ hlt
        have h_prop_y := sigma_props ctx y my h_my_lt_y
          (Finset.mem_filter.mp (Finset.min'_mem (mClass y) hm_ne_y)).2
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
      have hn_min_y : ¬ IsMin y := fun h ↦ lt_irrefl x (lt_of_lt_of_le hlt (h (le_of_lt hlt)))
      have hL_y : lOf ctx y = IsGreenL.eqvClass (σ.σ x y) := by
        rw [lOf, dif_neg hn_min_y]
        exact lOf_well_defined ctx y _ x (Classical.choose_spec (not_isMin_iff.mp hn_min_y)) hlt
      have hn_max_x : ¬ IsMax x := fun h ↦ lt_irrefl y (lt_of_le_of_lt (h (le_of_lt hlt)) hlt)
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

def jUp (a : S) : Set S := { b | GreenJClass.mk a ≤ GreenJClass.mk b }

def labelingIn {α : Type*} [LinearOrder α]
    (σ : MultiplicativeLabeling S α) (U : Set S) : Prop :=
  ∀ x y : α, x < y → σ.σ x y ∈ U

lemma irregular_d_class_no_three_seq [Finite S] (a : S) {α : Type*} [LinearOrder α]
    (σ : MultiplicativeLabeling S α) (x y z : α)
    (h_img : labelingIn σ (jUp a))
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
  let currentCost := nD (IsGreenD.eqvClass x)
  let strictlyAbove := Finset.univ.filter
    (fun (y : S) => GreenJClass.mk x < GreenJClass.mk y)
  let maxAbove := strictlyAbove.attach.sup (fun ⟨y, _hy⟩ => nSElement y)
  currentCost + maxAbove
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

def OpenIntervalType {α : Type*} [LinearOrder α] (xs : List α) (i : ℕ) : Type _ :=
  { y : α // ∃ (h1 : i < xs.length) (h2 : i + 1 < xs.length),
    xs.get ⟨i, h1⟩ < y ∧ y < xs.get ⟨i + 1, h2⟩ }
  deriving LinearOrder

open Classical in
noncomputable instance instFintypeOpenInterval {α : Type*} [LinearOrder α] [Fintype α]
    (xs : List α) (i : ℕ) :
    Fintype (OpenIntervalType xs i) := by
  unfold OpenIntervalType
  classical
  infer_instance

open Classical in
noncomputable instance instFintypeSubtypeX {α : Type*} [LinearOrder α] [Fintype α]
    (xs : List α) :
    Fintype {x : α // x ∈ xs} := by
  classical
  infer_instance

noncomputable def regularSplits {α S : Type*}
    [LinearOrder α] [Fintype α] [Nonempty α] [Semigroup S] [Fintype S]
    (a : S) (xs : List α) [Nonempty {x // x ∈ xs}]
    [Nonempty (Fin (nD (IsGreenD.eqvClass a)))]
    (sX : Split {x // x ∈ xs} (nD (IsGreenD.eqvClass a)))
    (sY : ∀ (i : ℕ) [Nonempty (OpenIntervalType xs i)],
      Split (OpenIntervalType xs i) (nSElement a)) :
    Split α (nSElement a) := fun x =>
  if hx : x ∈ xs then
    ⟨(sX ⟨x, hx⟩).val + (nSElement a - nD (IsGreenD.eqvClass a)), by
      have := (sX ⟨x, hx⟩).isLt
      rw [nSElement]
      omega⟩
  else if h_ex : ∃ i, ∃ (h1 : i < xs.length) (h2 : i + 1 < xs.length),
      xs.get ⟨i, h1⟩ < x ∧ x < xs.get ⟨i + 1, h2⟩ then
    @sY (Classical.choose h_ex) ⟨⟨x, Classical.choose_spec h_ex⟩⟩
      ⟨x, Classical.choose_spec h_ex⟩
  else
    ⟨0, nSElement_pos a⟩

lemma regularSplits_props {α S : Type*}
    [LinearOrder α] [Fintype α] [Nonempty α] [Semigroup S] [Fintype S]
    (a : S) (xs : List α) [Nonempty {x // x ∈ xs}]
    [Nonempty (Fin (nD (IsGreenD.eqvClass a)))]
    (σ : MultiplicativeLabeling S α)
    (σ_X : MultiplicativeLabeling S {x // x ∈ xs})
    (σ_Y : ∀ (i : ℕ), MultiplicativeLabeling S (OpenIntervalType xs i))
    (sX : Split {x // x ∈ xs} (nD (IsGreenD.eqvClass a)))
    (sY : ∀ (i : ℕ) [Nonempty (OpenIntervalType xs i)],
      Split (OpenIntervalType xs i) (nSElement a))
    (hsX_ramsey : IsRamsey σ_X sX)
    (hsY_ramsey : ∀ (i : ℕ) [Nonempty (OpenIntervalType xs i)], IsRamsey (σ_Y i) (sY i))
    (h_min_in : (Finset.min' (Finset.univ : Finset α) Finset.univ_nonempty) ∈ xs)
    (h_σ_X : ∀ x y, σ_X.σ x y = σ.σ x.val y.val)
    (h_σ_Y : ∀ i x y, (σ_Y i).σ x y = σ.σ x.val y.val)
    (h_cov : ∀ x, x ∉ xs →
      ∃ (i : ℕ) (h1 : i < xs.length) (h2 : i + 1 < xs.length),
        xs.get ⟨i, h1⟩ < x ∧ x < xs.get ⟨i + 1, h2⟩)
    (hsY_strict : ∀ (i : ℕ) [Nonempty (OpenIntervalType xs i)]
      (z : OpenIntervalType xs i),
      (sY i z).val < nSElement a - nD (IsGreenD.eqvClass a))
    (h_interval_ramsey : ∀ x y, x ∉ xs → x < y →
      SplitRelation (regularSplits a xs sX sY) x y →
      ∃ (i : ℕ) (x_val y_val : OpenIntervalType xs i),
        x_val.val = x ∧ y_val.val = y ∧ SplitRelation (@sY i ⟨x_val⟩) x_val y_val)
    (h_min_sX : (sX ⟨Finset.min' (Finset.univ : Finset α) Finset.univ_nonempty,
      h_min_in⟩).val = nD (IsGreenD.eqvClass a) - 1)
    (h_max_val : (Finset.max' (Finset.univ : Finset (Fin (nSElement a)))
      Finset.univ_nonempty).val = nSElement a - 1)
    (h_N_pos : 0 < nD (IsGreenD.eqvClass a))
    (h_N_le_M : nD (IsGreenD.eqvClass a) ≤ nSElement a) :
    IsNormalized (regularSplits a xs sX sY) ∧
    IsRamsey σ (regularSplits a xs sX sY) := by
  constructor
  · ext
    simp only [regularSplits, h_min_in, ↓reduceDIte, h_min_sX, h_max_val]
    omega
  · intro x y hlt hsr
    have rank_lt_diff_of_not_mem : ∀ z, z ∉ xs →
        (regularSplits a xs sX sY z).val < nSElement a - nD (IsGreenD.eqvClass a) := by
      intro z hz
      have h_ex := h_cov z hz
      simp only [regularSplits, hz, h_ex, ↓reduceDIte]
      exact @hsY_strict _ ⟨⟨z, Classical.choose_spec h_ex⟩⟩ ⟨z, Classical.choose_spec h_ex⟩
    by_cases hx : x ∈ xs
    · have hy : y ∈ xs := by
        by_contra hny
        specialize rank_lt_diff_of_not_mem y hny
        have rank_eq : (regularSplits a xs sX sY x).val = (regularSplits a xs sX sY y).val :=
          congrArg Fin.val hsr.left
        have val_x_eq : (regularSplits a xs sX sY x).val =
            (sX ⟨x, hx⟩).val + (nSElement a - nD (IsGreenD.eqvClass a)) := by
          simp only [regularSplits, hx, ↓reduceDIte]
        omega
      have hsr_X : SplitRelation sX ⟨x, hx⟩ ⟨y, hy⟩ := by
        constructor
        · ext
          simpa [regularSplits, hx, hy] using hsr.left
        · intro z hz1 hz2
          have h_le : (⟨x, hx⟩ : {x // x ∈ xs}) ≤ ⟨y, hy⟩ := le_of_lt hlt
          simpa [regularSplits, hx, z.property, min_eq_left (le_of_lt hlt), min_eq_left h_le] using
            hsr.right z.val (by aesop) (by aesop)
      simpa only [h_σ_X] using hsX_ramsey ⟨x, hx⟩ ⟨y, hy⟩ hlt hsr_X
    · obtain ⟨i, x_val, y_val, rfl, rfl, hsr_Y⟩ := h_interval_ramsey x y hx hlt hsr
      simpa only [h_σ_Y] using @hsY_ramsey i ⟨x_val⟩ x_val y_val hlt hsr_Y

noncomputable def irregularSplits {α S : Type*}
    [LinearOrder α] [Fintype α] [Nonempty α] [Semigroup S] [Fintype S]
    (a : S) (xs : List α)
    (sY : ∀ (i : ℕ) [Nonempty (OpenIntervalType xs i)],
      Split (OpenIntervalType xs i) (nSElement a)) :
    Split α (nSElement a) := fun x =>
  if hx : x ∈ xs then
    ⟨nSElement a - 1, by
      have := nSElement_pos a
      omega
    ⟩
  else if h_ex : ∃ i, ∃ (h1 : i < xs.length) (h2 : i + 1 < xs.length),
      xs.get ⟨i, h1⟩ < x ∧ x < xs.get ⟨i + 1, h2⟩ then
    @sY (Classical.choose h_ex) ⟨⟨x, Classical.choose_spec h_ex⟩⟩
      ⟨x, Classical.choose_spec h_ex⟩
  else
    ⟨0, nSElement_pos a⟩

lemma irregularSplits_props {α S : Type*}
    [LinearOrder α] [Fintype α] [Nonempty α] [Semigroup S] [Fintype S]
    (a : S) (xs : List α)
    (σ : MultiplicativeLabeling S α)
    (σ_Y : ∀ (i : ℕ), MultiplicativeLabeling S (OpenIntervalType xs i))
    (sY : ∀ (i : ℕ) [Nonempty (OpenIntervalType xs i)],
    Split (OpenIntervalType xs i) (nSElement a))
    (hsY_ramsey : ∀ (i : ℕ) [Nonempty (OpenIntervalType xs i)], IsRamsey (σ_Y i) (sY i))
    (h_min_in : (Finset.min' (Finset.univ : Finset α) Finset.univ_nonempty) ∈ xs)
    (h_max_val : (Finset.max' (Finset.univ : Finset (Fin (nSElement a)))
    Finset.univ_nonempty).val = nSElement a - 1)
    (h_σ_Y : ∀ i x y, (σ_Y i).σ x y = σ.σ x.val y.val)
    (h_cov : ∀ x, x ∉ xs →
    ∃ (i : ℕ) (h1 : i < xs.length) (h2 : i + 1 < xs.length),
    xs.get ⟨i, h1⟩ < x ∧ x < xs.get ⟨i + 1, h2⟩)
    (hsY_strict : ∀ (i : ℕ) [Nonempty (OpenIntervalType xs i)],
    ∀ z : OpenIntervalType xs i, (sY i z).val < nSElement a - 1)
    (h_interval_ramsey : ∀ x y, x ∉ xs → x < y →
    SplitRelation (irregularSplits a xs sY) x y →
    ∃ (i : ℕ) (x_val y_val : OpenIntervalType xs i),
    x_val.val = x ∧ y_val.val = y ∧ SplitRelation (@sY i ⟨x_val⟩) x_val y_val)
    (h_X_ramsey : ∀ x y, x ∈ xs → y ∈ xs → x < y →
    SplitRelation (irregularSplits a xs sY) x y →
    σ.σ x y * σ.σ x y = σ.σ x y) :
    IsNormalized (irregularSplits a xs sY) ∧
    IsRamsey σ (irregularSplits a xs sY) := by
  constructor
  · ext
    simp only [irregularSplits, h_min_in, ↓reduceDIte, h_max_val]
  · intro x y hlt hsr
    have rank_lt_of_not_mem : ∀ z, z ∉ xs →
        (irregularSplits a xs sY z).val < nSElement a - 1 := by
      intro z hz
      have h_ex := h_cov z hz
      simp only [irregularSplits, hz, h_ex, ↓reduceDIte]
      exact @hsY_strict _ ⟨⟨z, Classical.choose_spec h_ex⟩⟩ ⟨z, Classical.choose_spec h_ex⟩
    by_cases hx : x ∈ xs
    · have hy : y ∈ xs := by
        by_contra hny
        specialize rank_lt_of_not_mem y hny
        have rank_eq : (irregularSplits a xs sY x).val = (irregularSplits a xs sY y).val :=
          congrArg Fin.val hsr.left
        have val_x_eq : (irregularSplits a xs sY x).val = nSElement a - 1 := by
          simp only [irregularSplits, hx, ↓reduceDIte]
        omega
      exact h_X_ramsey x y hx hy hlt hsr
    · obtain ⟨i, x_val, y_val, rfl, rfl, hsr_Y⟩ := h_interval_ramsey x y hx hlt hsr
      simpa only [h_σ_Y] using @hsY_ramsey i ⟨x_val⟩ x_val y_val hlt hsr_Y

lemma buildXSeq_covers {S α : Type*} [Semigroup S] [LinearOrder α] [Fintype α]
    (a : S) (σ : MultiplicativeLabeling S α) (x₀ : α) (x : α) :
    x ∉ buildXSeq a σ x₀ →
    ∃ (i : ℕ) (h1 : i < (buildXSeq a σ x₀).length) (h2 : i + 1 < (buildXSeq a σ x₀).length),
      (buildXSeq a σ x₀).get ⟨i, h1⟩ < x ∧ x < (buildXSeq a σ x₀).get ⟨i + 1, h2⟩ := by
  sorry

lemma simon_split_regular_case {S : Type*} [Semigroup S] [Fintype S]
    (a : S) {α : Type*} [LinearOrder α] [Fintype α] [Nonempty α]
    (σ : MultiplicativeLabeling S α) (_h_img : labelingIn σ (jUp a))
    (h_reg : IsRegularDClass (IsGreenD.eqvClass a))
    (ih : ∀ b : S, nSElement b < nSElement a →
    ∀ (xs : List α) (i : ℕ) [Nonempty (OpenIntervalType xs i)]
    (σ_β : MultiplicativeLabeling S (OpenIntervalType xs i)), labelingIn σ_β (jUp b) →
    ∃ (s : Split (OpenIntervalType xs i) (nSElement b)), IsNormalized s ∧ IsRamsey σ_β s) :
    ∃ (s : Split α (nSElement a)), IsNormalized s ∧ IsRamsey σ s := by
      let x₀ := Finset.min' (Finset.univ : Finset α) Finset.univ_nonempty
      let xs := buildXSeq a σ x₀
      have h_X_ne : xs ≠ [] := by
        intro h_eq
        unfold xs at h_eq
        rw [buildXSeq] at h_eq
        dsimp only at h_eq
        split at h_eq
        · contradiction
        · contradiction
      haveI instX : Nonempty { x // x ∈ xs } := by
        cases h : xs
        · exact False.elim (h_X_ne h)
        · next hd tl => exact ⟨⟨hd, by simp⟩⟩
      let σ_X : MultiplicativeLabeling S { x // x ∈ xs } :=
        ⟨fun x y ↦ σ.σ x y, fun x y z hxy hyz ↦ σ.prop x y z hxy hyz⟩
      let Y_α (i : Nat) := OpenIntervalType xs i
      let σ_Y (i : Nat) : MultiplicativeLabeling S (Y_α i) :=
        ⟨fun y z ↦ σ.σ y.1 z.1, fun y z w hyz hzw ↦ σ.prop y.1 z.1 w.1 hyz hzw⟩
      have h_min_in : x₀ ∈ xs := by
        change x₀ ∈ buildXSeq a σ x₀
        rw [buildXSeq]
        split
        · simp
        · simp
      have h_min_in_alpha : (Finset.min' Finset.univ (Finset.univ_nonempty (α := α))) ∈ xs :=
        h_min_in
      have h_σ_X_eq : ∀ x y, σ_X.σ x y = σ.σ x.val y.val := fun _ _ ↦ rfl
      have h_σ_Y_eq : ∀ i x y, (σ_Y i).σ x y = σ.σ x.val y.val := fun _ _ _ ↦ rfl
      have h_nD_pos : 0 < nD (IsGreenD.eqvClass a) :=
        nD_pos (IsGreenD.eqvClass a) ⟨a, rfl⟩
      haveI instFinFin : Nonempty (Fin (nD (IsGreenD.eqvClass a))) := ⟨⟨0, h_nD_pos⟩⟩
      have h_X_split : ∃ sX : Split {x // x ∈ xs} (nD (IsGreenD.eqvClass a)),
          IsNormalized sX ∧ IsRamsey σ_X sX := by
        have h_range : ∀ (x y : {x // x ∈ xs}), x < y → σ_X.σ x y ∈ IsGreenD.eqvClass a := by
          sorry
        exact simon_regular_d_case σ_X (IsGreenD.eqvClass a) ⟨a, rfl⟩ h_reg h_range
      have h_Y_strict : ∀ (i : Nat) [h : Nonempty (Y_α i)],
          labelingIn (σ_Y i) {b | GreenJClass.mk a < GreenJClass.mk b} := by
        intro i h_ne x y h_lt
        sorry
      have h_Y_splits : ∀ (i : Nat) [h : Nonempty (Y_α i)],
          ∃ (sY : Split (Y_α i) (nSElement a)),
          IsNormalized sY ∧ IsRamsey (σ_Y i) sY := by
        intro i h_ne
        have h_b_exists : ∃ (b : S), labelingIn (σ_Y i) (jUp b) ∧ nSElement b < nSElement a := by
          sorry
        obtain ⟨b, hb_img, hb_lt⟩ := h_b_exists
        obtain ⟨sY_b, hsY_norm, hsY_ramsey⟩ := ih b hb_lt xs i (σ_Y i) hb_img
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
      let s := regularSplits a xs sX sY_fun
      use s
      have h_cov : ∀ x ∉ xs, ∃ i h1 h2, xs.get ⟨i, h1⟩ < x ∧ x < xs.get ⟨i + 1, h2⟩ := by
        intro x hnx
        exact buildXSeq_covers a σ x₀ x hnx
      have hsY_strict : ∀ (i : ℕ) [inst : Nonempty (Y_α i)] (z : Y_α i),
          (sY_fun i z).val < nSElement a - nD (IsGreenD.eqvClass a) := sorry
      have h_interval_ramsey : ∀ x y, x ∉ xs → x < y → SplitRelation s x y →
        ∃ (i : ℕ) (xv yv : Y_α i),
          xv.val = x ∧ yv.val = y ∧ SplitRelation (@sY_fun i ⟨xv⟩) xv yv := sorry
      have h_min_sX :
        (sX ⟨Finset.min' _ Finset.univ_nonempty, h_min_in⟩).val =
          nD (IsGreenD.eqvClass a) - 1 := sorry
      have h_max_val : (Finset.max' (Finset.univ : Finset (Fin (nSElement a)))
        Finset.univ_nonempty).val = nSElement a - 1 := sorry
      have h_N_pos : 0 < nD (IsGreenD.eqvClass a) := h_nD_pos
      have h_N_le_M : nD (IsGreenD.eqvClass a) ≤ nSElement a := sorry
      constructor
      · exact (regularSplits_props a xs σ σ_X σ_Y sX sY_fun hsX_ramsey
          hsY_ramsey h_min_in_alpha h_σ_X_eq h_σ_Y_eq h_cov hsY_strict
            h_interval_ramsey h_min_sX h_max_val h_N_pos h_N_le_M).1
      · exact (regularSplits_props a xs σ σ_X σ_Y sX sY_fun hsX_ramsey
          hsY_ramsey h_min_in_alpha h_σ_X_eq h_σ_Y_eq h_cov hsY_strict
            h_interval_ramsey h_min_sX h_max_val h_N_pos h_N_le_M).2

lemma simon_split_irregular_case {S : Type*} [Semigroup S] [Fintype S]
    (a : S) {α : Type*} [LinearOrder α] [Fintype α] [Nonempty α]
    (σ : MultiplicativeLabeling S α) (_h_img : labelingIn σ (jUp a))
    (_h_not_reg : ¬ IsRegularDClass (IsGreenD.eqvClass a))
    (ih : ∀ b : S, nSElement b < nSElement a →
    ∀ (xs : List α) (i : ℕ) [Nonempty (OpenIntervalType xs i)]
    (σ_β : MultiplicativeLabeling S (OpenIntervalType xs i)), labelingIn σ_β (jUp b) →
    ∃ (s : Split (OpenIntervalType xs i) (nSElement b)), IsNormalized s ∧ IsRamsey σ_β s) :
    ∃ (s : Split α (nSElement a)), IsNormalized s ∧ IsRamsey σ s := by
      let x₀ := Finset.min' (Finset.univ : Finset α) Finset.univ_nonempty
      let xs := buildXSeq a σ x₀
      have h_X_ne : xs ≠ [] := by
        intro h_eq
        unfold xs at h_eq
        rw [buildXSeq] at h_eq
        dsimp only at h_eq
        split at h_eq
        · contradiction
        · contradiction
      haveI instX : Nonempty { x // x ∈ xs } := by
        cases h : xs
        · exact False.elim (h_X_ne h)
        · next hd tl => exact ⟨⟨hd, by simp⟩⟩
      let Y_α (i : Nat) := OpenIntervalType xs i
      let σ_Y (i : Nat) : MultiplicativeLabeling S (Y_α i) :=
        ⟨fun y z ↦ σ.σ y.1 z.1, fun y z w hyz hzw ↦ σ.prop y.1 z.1 w.1 hyz hzw⟩
      have h_min_in : x₀ ∈ xs := by
        change x₀ ∈ buildXSeq a σ x₀
        rw [buildXSeq]
        split
        · simp
        · simp
      have h_min_in_alpha : (Finset.min' Finset.univ (Finset.univ_nonempty (α := α))) ∈ xs :=
        h_min_in
      have h_σ_Y_eq : ∀ i x y, (σ_Y i).σ x y = σ.σ x.val y.val := fun _ _ _ ↦ rfl
      have h_Y_strict : ∀ (i : Nat) [h : Nonempty (Y_α i)],
          labelingIn (σ_Y i) {b | GreenJClass.mk a < GreenJClass.mk b} := by
        intro i h_ne x y h_lt
        sorry
      have h_Y_splits : ∀ (i : Nat) [h : Nonempty (Y_α i)],
          ∃ (sY : Split (Y_α i) (nSElement a)),
          IsNormalized sY ∧ IsRamsey (σ_Y i) sY := by
        intro i h_ne
        have h_b_exists : ∃ (b : S), labelingIn (σ_Y i) (jUp b) ∧ nSElement b < nSElement a := by
          sorry
        obtain ⟨b, hb_img, hb_lt⟩ := h_b_exists
        obtain ⟨sY_b, hsY_norm, hsY_ramsey⟩ := ih b hb_lt xs i (σ_Y i) hb_img
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
      let s := irregularSplits a xs sY_fun
      use s
      have h_cov : ∀ x ∉ xs, ∃ i h1 h2, xs.get ⟨i, h1⟩ < x ∧ x < xs.get ⟨i + 1, h2⟩ := by
        intro x hnx
        exact buildXSeq_covers a σ x₀ x hnx
      have hsY_strict : ∀ (i : ℕ) [inst : Nonempty (Y_α i)] (z : Y_α i),
          (sY_fun i z).val < nSElement a - 1 := sorry
      have h_interval_ramsey : ∀ x y, x ∉ xs → x < y → SplitRelation s x y →
        ∃ (i : ℕ) (xv yv : Y_α i),
          xv.val = x ∧ yv.val = y ∧ SplitRelation (@sY_fun i ⟨xv⟩) xv yv := sorry
      have h_max_val : (Finset.max' (Finset.univ : Finset (Fin (nSElement a)))
        Finset.univ_nonempty).val = nSElement a - 1 := sorry
      have h_X_ramsey : ∀ x y, x ∈ xs → y ∈ xs → x < y → SplitRelation s x y →
          σ.σ x y * σ.σ x y = σ.σ x y := sorry
      constructor
      · exact (irregularSplits_props a xs σ σ_Y sY_fun hsY_ramsey
          h_min_in_alpha h_max_val h_σ_Y_eq h_cov hsY_strict
            h_interval_ramsey h_X_ramsey).1
      · exact (irregularSplits_props a xs σ σ_Y sY_fun hsY_ramsey
          h_min_in_alpha h_max_val h_σ_Y_eq h_cov hsY_strict
            h_interval_ramsey h_X_ramsey).2

lemma simon_split_induction_aux {S : Type*} [Semigroup S] [Fintype S]
    (n : ℕ) :
    ∀ (a : S) (_hn : nSElement a ≤ n)
    {α : Type*} [LinearOrder α] [Fintype α] [Nonempty α]
    (σ : MultiplicativeLabeling S α)
    (_h_img : labelingIn σ (jUp a)),
    ∃ (s : Split α (nSElement a)), IsNormalized s ∧ IsRamsey σ s := by
  induction n using Nat.strong_induction_on with
  | h n ihn =>
    intro a _ α _ _ _ σ h_img
    have ih : ∀ b : S, nSElement b < nSElement a →
              ∀ (xs : List α) (i : ℕ) [Nonempty (OpenIntervalType xs i)]
              (σ_β : MultiplicativeLabeling S (OpenIntervalType xs i)), labelingIn σ_β (jUp b) →
              ∃ (s : Split (OpenIntervalType xs i) (nSElement b)),
                IsNormalized s ∧ IsRamsey σ_β s := by
                  intro b _hb xs i _h_ne_i σ_β h_img_β
                  apply ihn (nSElement b)
                  · omega
                  · exact le_rfl
                  · exact h_img_β
    by_cases h_reg : IsRegularDClass (IsGreenD.eqvClass a)
    · exact simon_split_regular_case a σ h_img h_reg ih
    · exact simon_split_irregular_case a σ h_img h_reg ih

lemma simon_split_induction (a : S) {α : Type*} [LinearOrder α] [Fintype α] [Nonempty α]
    (σ : MultiplicativeLabeling S α)
    (h_img : labelingIn σ (jUp a)) :
    ∃ (s : Split α (nSElement a)), IsNormalized s ∧ IsRamsey σ s :=
  simon_split_induction_aux (nSElement a) a le_rfl σ h_img

theorem simon_split {S α : Type*} [Semigroup S] [Fintype S]
    [LinearOrder α] [Fintype α] [Nonempty α] [Nonempty (Fin (nS S))]
    (σ : MultiplicativeLabeling S α) :
    ∃ (s : Split α (nS S)), IsNormalized s ∧ IsRamsey σ s := by
  let x₀ := Finset.min' (Finset.univ : Finset α) Finset.univ_nonempty
  let y₀ := Finset.max' (Finset.univ : Finset α) Finset.univ_nonempty
  let a := σ.σ x₀ y₀
  have ha : labelingIn σ (jUp a) := by
    intros x y hlt
    have hx0 : x₀ ≤ x := Finset.min'_le _ _ (Finset.mem_univ _)
    have hy0 : y ≤ y₀ := Finset.le_max' _ _ (Finset.mem_univ _)
    change IsGreenJRel (σ.σ x₀ y₀) (σ.σ x y)
    rcases hx0.eq_or_lt with rfl | hx0_lt
    · rcases hy0.eq_or_lt with rfl | hy0_lt
      · exact IsGreenJRel.eq rfl
      · have h_prop := σ.prop _ y y₀ hlt hy0_lt
        exact IsGreenJRel.mul_right (σ.σ y y₀) h_prop.symm
    · rcases hy0.eq_or_lt with rfl | hy0_lt
      · have h_prop := σ.prop x₀ x _ hx0_lt hlt
        exact IsGreenJRel.mul_left (σ.σ x₀ x) h_prop.symm
      · have h1 := σ.prop x₀ x y hx0_lt hlt
        have h2 := σ.prop x₀ y y₀ (lt_trans hx0_lt hlt) hy0_lt
        exact IsGreenJRel.mul_both (σ.σ x₀ x) (σ.σ y y₀) (by rw [← h2, ← h1])
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
