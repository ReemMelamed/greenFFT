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

theorem simon_group_case (σ : MultiplicativeLabeling G α) :
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


section RegularDClassCase

variable {S α : Type*} [Semigroup S] [Fintype S] [LinearOrder α] [Fintype α] [Nonempty α]

-- Lemma 3.3
theorem simon_regular_d_case
    (σ : MultiplicativeLabeling S α)
    (D : Set S)
    (hD : ∃ x, D = greenDClass x)
    (_ : IsRegularDClass D)
    (h_range : ∀ x y, x < y → σ.σ x y ∈ D) :
    ∃ (s : Split α (nD D)), IsNormalized s ∧ IsRamsey σ s := by
  sorry

end RegularDClassCase
