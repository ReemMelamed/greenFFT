/- Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz -/

import Semigroup.GreensRelations.MulSeq
import Mathlib.Data.Fintype.Card

/-!
# Main Theorems of Green's Relations

This file proves the major structural theorems regarding Green's relations,
including Green's Lemma (bijections between H-classes), the equivalence of D and J
in finite semigroups, and conditions for H-classes to be subgroups.

## Main results

* `isRegularDClass_iff_exists_idempotent`:
    A `D`-class is regular if and only if it contains an idempotent.
* `equivHClassOfIsGreenL` / `equivHClassOfIsGreenR`:
    Green's Lemma, providing bijections between
        `H`-classes contained in the same `L`-class or `R`-class.
* `card_greenHClass_eq_of_isGreenD`:
    All `H`-classes within the same `D`-class have the same cardinality.
* `isGreenD_eq_isGreenJ_of_finite`: In a finite semigroup, Green's `D` and `J` relations coincide.
* `isGroup_isGreenH_eqvClass_iff_idempotent`:
    Green's Theorem stating that an `H`-class is a subgroup
        if and only if it contains an idempotent.

## References

* [T. Colombet, *The Factorization Forest Theorem*][colombet2008]

## Tags

green's relations, green's lemma, green's theorem, finite semigroup, regular class, idempotent
-/

variable {S : Type*} [Semigroup S]

open MulSeq

/-- A `D`-class is regular if and only if it contains an idempotent. -/
theorem isRegularDClass_iff_exists_idempotent [Finite S]
  (D : Set S) (hD : ∃ x, D = IsGreenD.eqvClass x) :
    IsRegularDClass D ↔ ∃ e ∈ D, e * e = e := by
  obtain ⟨x₀, rfl⟩ := hD
  constructor
  · intro hReg
    have hx₀_in : x₀ ∈ IsGreenD.eqvClass x₀ := IsGreenD.refl x₀
    obtain ⟨s, hs⟩ := hReg x₀ hx₀_in
    let e := x₀ * s
    have he_idem : e * e = e := by grind
    have he_R_x₀ : IsGreenR e x₀ := by
      constructor
      · right; exact ⟨s, rfl⟩
      · right; exact ⟨x₀, hs.symm⟩
    have he_D_x₀ : IsGreenD e x₀ := ⟨e, IsGreenL.refl e, he_R_x₀⟩
    exact ⟨e, he_D_x₀, he_idem⟩
  · rintro ⟨e, heD, he_idem⟩
    intro y hyD
    have h_ye : IsGreenD y e := IsGreenD.trans hyD (IsGreenD.symm heD)
    obtain ⟨z, hL_yz, hR_ze⟩ := h_ye
    have h_ez_z : e * z = z := by
      rcases hR_ze.left with rfl | ⟨v, hv⟩ <;> grind [mul_assoc]
    have hz_reg : ∃ u, z * u * z = z := by
      rcases hR_ze.right with rfl | ⟨u, hu⟩
      · exact ⟨e, by simp [he_idem]⟩
      · exact ⟨u, by simp [← hu, h_ez_z]⟩
    obtain ⟨u, hu_z⟩ := hz_reg
    have hy_uz : y * u * z = y := by
      rcases hL_yz.left with rfl | ⟨p, hp⟩ <;> grind [mul_assoc]
    rcases hL_yz.right with rfl | ⟨q, hq⟩
    · exact ⟨u, hy_uz⟩
    · use u * q
      rw [← mul_assoc y u q, mul_assoc (y * u) q y, ← hq, hy_uz]

/-- A bijection between the `H`-classes of two `L`-related elements. -/
noncomputable def equivHClassOfIsGreenL {a b : S} (h_L_ab : IsGreenL a b) :
    IsGreenH.eqvClass a ≃ IsGreenH.eqvClass b := by
  by_cases ha_eq_b : a = b
  · exact ha_eq_b ▸ Equiv.refl _
  · have h_exists_w : ∃ w, a = w * b := h_L_ab.left.resolve_left ha_eq_b
    let w := Classical.choose h_exists_w
    have ha_eq_wb : a = w * b := Classical.choose_spec h_exists_w
    have hb_ne_a : b ≠ a := Ne.symm ha_eq_b
    have h_exists_z : ∃ z, b = z * a := h_L_ab.right.resolve_left hb_ne_a
    let z := Classical.choose h_exists_z
    have hb_eq_za : b = z * a := Classical.choose_spec h_exists_z
    have hwza_eq_a : w * z * a = a := by rw [mul_assoc, ← hb_eq_za, ← ha_eq_wb]
    have hzwb_eq_b : z * w * b = b := by rw [mul_assoc, ← ha_eq_wb, ← hb_eq_za]
    exact {
      toFun := fun ⟨x, hx_in_H⟩ ↦ ⟨z * x, by
        have hR_zx_za : IsGreenR (z * x) (z * a) := IsGreenR.mul_left z hx_in_H.right
        have hR_zx_b : IsGreenR (z * x) b := by rwa [← hb_eq_za] at hR_zx_za
        have hwzx_eq_x : w * z * x = x := IsGreenR.cancellation hx_in_H.right hwza_eq_a
        have hL_zx_x : IsGreenL (z * x) x :=
          ⟨Or.inr ⟨z, rfl⟩, Or.inr ⟨w, by simp [← mul_assoc, hwzx_eq_x]⟩⟩
        have hL_zx_b : IsGreenL (z * x) b :=
          IsGreenL.trans hL_zx_x (IsGreenL.trans hx_in_H.left h_L_ab)
        exact ⟨hL_zx_b, hR_zx_b⟩⟩
      invFun := fun ⟨y, hy_in_H⟩ ↦ ⟨w * y, by
        have hR_wy_wb : IsGreenR (w * y) (w * b) := IsGreenR.mul_left w hy_in_H.right
        have hR_wy_a : IsGreenR (w * y) a := by rwa [← ha_eq_wb] at hR_wy_wb
        have hzwy_eq_y : z * w * y = y := IsGreenR.cancellation hy_in_H.right hzwb_eq_b
        have hdvd_wy_y : IsGreenLeftDvd (w * y) y := Or.inr ⟨w, rfl⟩
        have hdvd_y_wy : IsGreenLeftDvd y (w * y) := Or.inr ⟨z, by rw [← mul_assoc, hzwy_eq_y]⟩
        have hL_wy_y : IsGreenL (w * y) y := ⟨hdvd_wy_y, hdvd_y_wy⟩
        have hL_wy_a : IsGreenL (w * y) a := IsGreenL.trans hL_wy_y
            (IsGreenL.trans hy_in_H.left (IsGreenL.symm h_L_ab))
        exact ⟨hL_wy_a, hR_wy_a⟩⟩
      left_inv := fun ⟨x, hx_in_H⟩ ↦ Subtype.ext (by
        dsimp only
        rw [← mul_assoc]
        exact IsGreenR.cancellation hx_in_H.right hwza_eq_a)
      right_inv := fun ⟨y, hy_in_H⟩ ↦ Subtype.ext (by
        dsimp only
        rw [← mul_assoc]
        exact IsGreenR.cancellation hy_in_H.right hzwb_eq_b)
    }

open MulOpposite in
/-- A bijection between the `H`-classes of two `R`-related elements. -/
noncomputable def equivHClassOfIsGreenR {a b : S} (h : IsGreenR a b) :
    IsGreenH.eqvClass a ≃ IsGreenH.eqvClass b :=
  (IsGreenH.equivHClassOp a).trans
      ((equivHClassOfIsGreenL (isGreenR_iff_isGreenL_op.mp h)).trans
      (IsGreenH.equivHClassOp b).symm)

open Classical in
/-- Any two `H`-classes within the same `D`-class have the same cardinality. -/
theorem card_greenHClass_eq_of_isGreenD [Fintype S] {a b : S} (h : IsGreenD a b) :
    Fintype.card (IsGreenH.eqvClass a) = Fintype.card (IsGreenH.eqvClass b) :=
  let ⟨_, hL, hR⟩ := h
  (Fintype.card_congr (equivHClassOfIsGreenL hL)).trans
      (Fintype.card_congr (equivHClassOfIsGreenR hR))

/-- If `a` and `b` are `J`-related in a finite semigroup, they are also `D`-related. -/
lemma isGreenD_of_isGreenJ [Finite S] {a b : S} (h : IsGreenJ a b) : IsGreenD a b := by
  rcases h with ⟨hab, hba⟩
  cases hab <;> cases hba <;>
    grind [isGreenD_of_left_left, isGreenD_of_left_right,
                     isGreenD_of_right_left, isGreenD_of_right_right,
                     isGreenD_of_JRel_left_both, isGreenD_of_JRel_right_both,
                     isGreenD_of_JRel_both, IsGreenD.refl, IsGreenD.symm]

/-- If `a` and `b` are `D`-related, they satisfy the basic `J`-relation step. -/
lemma isGreenJRel_of_isGreenD {a b : S} (h : IsGreenD a b) : IsGreenJRel a b := by
  rcases h with ⟨z, hL, hR⟩
  rcases hL.left with rfl | ⟨u, hu⟩
  · rcases hR.left with rfl | ⟨v, hv⟩
    · exact IsGreenJRel.eq rfl
    · exact IsGreenJRel.mul_right v hv
  · rcases hR.left with rfl | ⟨v, hv⟩
    · exact IsGreenJRel.mul_left u hu
    · exact IsGreenJRel.mul_both u v (by rw [hu, hv, mul_assoc])

/-- If `a` and `b` are `D`-related, they are also `J`-related. -/
lemma isGreenJ_of_isGreenD {a b : S} (h : IsGreenD a b) : IsGreenJ a b :=
  ⟨isGreenJRel_of_isGreenD h, isGreenJRel_of_isGreenD h.symm⟩

/-- In a finite semigroup, Green's `D` relation and Green's `J` relation are equal. -/
theorem isGreenD_eq_isGreenJ_of_finite [Finite S] : (IsGreenD : S → S → Prop) = IsGreenJ := by
  ext a b
  constructor
  · exact isGreenJ_of_isGreenD
  · exact isGreenD_of_isGreenJ

open MulOpposite in
/-- If `b` and `a * b` are `D`-related in a finite semigroup, they are `L`-related. -/
lemma isGreenL_sl_of_isGreenD_sl [Finite S] {a b : S} (h : IsGreenD b (a * b)) :
    IsGreenL b (a * b) := by
  have h_ab_dvd_b : IsGreenLeftDvd (a * b) b := Or.inr ⟨a, rfl⟩
  have h_b_dvd_ab : IsGreenLeftDvd b (a * b) := by
    rcases h with ⟨z', hL_bz', hR_z'ab⟩
    obtain ⟨z, hR_bz, hL_zab⟩ := isGreenL_commutes_isGreenR hL_bz' hR_z'ab
    obtain ⟨c, rfl, hc_dvd⟩ : ∃ c, z = c * b ∧ IsGreenLeftDvd c a := by
      rcases hL_zab.left with rfl | ⟨w, hw⟩
      · exact ⟨a, rfl, Or.inl rfl⟩
      · exact ⟨w * a, by rw [hw, ← mul_assoc], Or.inr ⟨w, rfl⟩⟩
    obtain ⟨i, j, hij, heq⟩ := leftMulSeq_pigeonhole c b
    have hR_all : ∀ n, IsGreenR b (leftMulSeq c b n) := by
      intro n; induction n with
      | zero => exact IsGreenR.refl b
      | succ n ih => exact IsGreenR.trans hR_bz (IsGreenR.mul_left c ih)
    have h_b_eq_ckb : ∃ k > 0, b = leftMulSeq c b k := by
      obtain ⟨k, hk_pos, hk_eq_j⟩ : ∃ k > 0, i + k = j := ⟨j - i, by omega, by omega⟩
      have hs : ∀ m, leftMulSeq c b (i + m) = leftMulSeq c (leftMulSeq c b i) m := by
        intro m; induction m with
        | zero => rfl
        | succ m ih => rw [← add_assoc]; exact congrArg (fun x ↦ c * x) ih
      have h_gi_k : leftMulSeq c (leftMulSeq c b i) k = leftMulSeq c b i := by
        rw [← hs k, hk_eq_j, ← heq]
      rcases (hR_all i).left with heq_b | ⟨v_outer, hv⟩
      · exact ⟨k, hk_pos, by grind⟩
      · exact ⟨k, hk_pos, by grind [leftMulSeq_mul_pull]⟩
    rcases h_b_eq_ckb with ⟨k, hk_pos, hk_eq⟩
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hk_pos)
    rcases hc_dvd with hc_eq_a | ⟨w, hw⟩
    · rcases m with _ | m_pred
      · exact Or.inl (by grind [leftMulSeq])
      · exact Or.inr ⟨leftMulSeq c c m_pred, by
          grind [leftMulSeq_mul_pull, leftMulSeq_pull_c]⟩
    · exact Or.inr ⟨leftMulSeq c w m, by
        grind [leftMulSeq_mul_pull, leftMulSeq_pull_c]⟩
  exact ⟨h_b_dvd_ab, h_ab_dvd_b⟩

open MulOpposite in
/-- If `a` and `a * b` are `D`-related in a finite semigroup, they are `R`-related. -/
lemma isGreenR_sr_of_isGreenD_sr [Finite S] {a b : S} (h : IsGreenD a (a * b)) :
    IsGreenR a (a * b) := by
  grind [op_mul, IsGreenD.isGreenD_iff_isGreenD_op,
      isGreenR_iff_isGreenL_op, isGreenL_sl_of_isGreenD_sl]

/-- If `a`, `b`, and `a * b` are all in the same regular `D`-class,
    then `a` is `R`-related to `a * b`, `b` is `L`-related to `a * b`,
    and there exists an idempotent `e` in the `D`-class such that `a`
    is `L`-related to `e` and `b` is `R`-related to `e`. -/
theorem mul_mem_isGreenD_eqvClass_properties
  [Finite S] {D : Set S} (hD_exists : ∃ x, D = IsGreenD.eqvClass x)
  (a b : S) (ha : a ∈ D) (hb : b ∈ D) (hab : a * b ∈ D) :
  (IsGreenR a (a * b) ∧ IsGreenL b (a * b)) ∧
  (∃ e ∈ D, e * e = e ∧ IsGreenL a e ∧ IsGreenR b e) := by
  obtain ⟨x₀, hx₀⟩ := hD_exists
  have hDa : a ∈ IsGreenD.eqvClass x₀ := hx₀ ▸ ha
  have hDb : b ∈ IsGreenD.eqvClass x₀ := hx₀ ▸ hb
  have hDab : a * b ∈ IsGreenD.eqvClass x₀ := hx₀ ▸ hab
  have h_a_D_ab : IsGreenD a (a * b) := IsGreenD.trans hDa (IsGreenD.symm hDab)
  have h_b_D_ab : IsGreenD b (a * b) := IsGreenD.trans hDb (IsGreenD.symm hDab)
  have hR_a_ab : IsGreenR a (a * b) := isGreenR_sr_of_isGreenD_sr h_a_D_ab
  have hL_b_ab : IsGreenL b (a * b) := isGreenL_sl_of_isGreenD_sl h_b_D_ab
  exact ⟨⟨hR_a_ab, hL_b_ab⟩, by
    have h_a_dvd : IsGreenRightDvd a (a * b) := hR_a_ab.left
    have h_b_dvd : IsGreenLeftDvd b (a * b) := hL_b_ab.left
    rcases h_a_dvd with ha_eq | ⟨u, hu⟩ <;> rcases h_b_dvd with hb_eq | ⟨v, hv⟩
    · exact ⟨a, ha, by grind, IsGreenL.refl a, by grind [IsGreenR.refl]⟩
    · have hLab : IsGreenL a b := ⟨Or.inr ⟨a, ha_eq⟩, Or.inr ⟨v, by grind⟩⟩
      exact ⟨b, hb, by grind, hLab, IsGreenR.refl b⟩
    · have hRba : IsGreenR b a := ⟨Or.inr ⟨b, hb_eq⟩, Or.inr ⟨u, by grind⟩⟩
      exact ⟨a, ha, by grind, IsGreenL.refl a, hRba⟩
    · have h_idem : (v * a) * (v * a) = v * a := by grind [mul_assoc]
      have hLae : IsGreenL a (v * a) := ⟨Or.inr ⟨a, by grind [mul_assoc]⟩, Or.inr ⟨v, rfl⟩⟩
      have hRbe : IsGreenR b (v * a) :=
        ⟨Or.inr ⟨b, by grind [mul_assoc]⟩, Or.inr ⟨u, by grind [mul_assoc]⟩⟩
      exact ⟨v * a, hx₀.symm ▸ IsGreenD.trans
          ⟨a, IsGreenL.symm hLae, IsGreenR.refl a⟩ hDa, h_idem, hLae, hRbe⟩
  ⟩

/-- An `H`-class is either a group or contains no idempotents
    and is not closed under multiplication. -/
lemma isGroup_isGreenH_eqvClass_iff_idempotent
    [Finite S] (H : Set S) (hH : ∃ a, H = IsGreenH.eqvClass a) :
    (∀ x y, x ∈ H → y ∈ H → x * y ∉ H) ∨
    (∃ e ∈ H, e * e = e ∧ ∀ x y, x ∈ H → y ∈ H → x * y ∈ H) := by
  obtain ⟨a, rfl⟩ := hH
  by_cases h : ∀ x y, x ∈ IsGreenH.eqvClass a → y ∈ IsGreenH.eqvClass a →
    x * y ∉ IsGreenH.eqvClass a
  · exact Or.inl h
  · right
    push_neg at h
    obtain ⟨x₀, y₀, hx₀, hy₀, hxy₀⟩ := h
    have hx₀H : IsGreenH x₀ a := hx₀
    have hy₀H : IsGreenH y₀ a := hy₀
    have hxy₀H : IsGreenH (x₀ * y₀) a := hxy₀
    have hx₀D : x₀ ∈ IsGreenD.eqvClass a := ⟨a, hx₀H.left, IsGreenR.refl a⟩
    have hy₀D : y₀ ∈ IsGreenD.eqvClass a := ⟨a, hy₀H.left, IsGreenR.refl a⟩
    have hxy₀D : x₀ * y₀ ∈ IsGreenD.eqvClass a := ⟨a, hxy₀H.left, IsGreenR.refl a⟩
    have hD_ex : Exists (fun y ↦ IsGreenD.eqvClass a = IsGreenD.eqvClass y) := ⟨a, rfl⟩
    obtain ⟨hRL_unused, e, heD, he_idem, hLx₀e, hRy₀e⟩ :=
      mul_mem_isGreenD_eqvClass_properties hD_ex x₀ y₀ hx₀D hy₀D hxy₀D
    have hLx₀a : IsGreenL x₀ a := hx₀H.left
    have hRy₀a : IsGreenR y₀ a := hy₀H.right
    have hLae : IsGreenL a e := IsGreenL.trans (IsGreenL.symm hLx₀a) hLx₀e
    have hRae : IsGreenR a e := IsGreenR.trans (IsGreenR.symm hRy₀a) hRy₀e
    have heH : e ∈ IsGreenH.eqvClass a := ⟨IsGreenL.symm hLae, IsGreenR.symm hRae⟩
    exact ⟨e, heH, he_idem, fun u v huH hvH ↦ by
      have hue : IsGreenH u e := IsGreenH.trans huH (IsGreenH.symm heH)
      have hve : IsGreenH v e := IsGreenH.trans hvH (IsGreenH.symm heH)
      have hLue : IsGreenL u e := hue.left
      have hRve : IsGreenR v e := hve.right
      have hev : e * v = v := by
        rcases hRve.left with rfl | ⟨z, hz⟩ <;> grind [mul_assoc]
      have hue_eq : u * e = u := by
        rcases hLue.left with rfl | ⟨w, hw⟩ <;> grind [mul_assoc]
      have hLuv_ev : IsGreenL (u * v) (e * v) := IsGreenL.mul_right v hLue
      have hLuv_v : IsGreenL (u * v) v := by rwa [hev] at hLuv_ev
      have hRuv_ue : IsGreenR (u * v) (u * e) := IsGreenR.mul_left u hRve
      have hRuv_u : IsGreenR (u * v) u := by rwa [hue_eq] at hRuv_ue
      have hLuv_a : IsGreenL (u * v) a := IsGreenL.trans hLuv_v hvH.left
      have hRuv_a : IsGreenR (u * v) a := IsGreenR.trans hRuv_u huH.right
      exact ⟨hLuv_a, hRuv_a⟩⟩
