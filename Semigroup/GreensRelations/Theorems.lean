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

## References

* [T. Colcombet, *The Factorization Forest Theorem*][colombet2008]
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
    obtain ⟨s, hs⟩ := hReg x₀ (IsGreenD.refl x₀)
    exact ⟨x₀ * s, ⟨x₀ * s, IsGreenL.refl _, ⟨Or.inr ⟨s, rfl⟩, Or.inr ⟨x₀, hs.symm⟩⟩⟩, by grind⟩
  · rintro ⟨e, heD, he_idem⟩ y hyD
    let ⟨z, hL_yz, hR_ze⟩ := hyD.trans heD.symm
    have h_ez_z : e * z = z := by rcases hR_ze.left with rfl | ⟨v, rfl⟩ <;> grind [mul_assoc]
    obtain ⟨u, hu_z⟩ : ∃ u, z * u * z = z := by
      rcases hR_ze.right with rfl | ⟨u, rfl⟩
      · exact ⟨e, by simp [he_idem]⟩
      · exact ⟨u, by simp [h_ez_z]⟩
    have hy_uz : y * u * z = y := by rcases hL_yz.left with rfl | ⟨p, rfl⟩ <;> grind [mul_assoc]
    rcases hL_yz.right with rfl | ⟨q, rfl⟩
    · exact ⟨u, hy_uz⟩
    · exact ⟨u * q, by grind [mul_assoc]⟩

/-- A bijection between the `H`-classes of two `L`-related elements. -/
noncomputable def equivHClassOfIsGreenL {a b : S} (h_L_ab : IsGreenL a b) :
    IsGreenH.eqvClass a ≃ IsGreenH.eqvClass b := by
  by_cases ha_eq_b : a = b
  · exact ha_eq_b ▸ Equiv.refl _
  · choose w hw using h_L_ab.left.resolve_left ha_eq_b
    choose z hz using h_L_ab.right.resolve_left (Ne.symm ha_eq_b)
    have hwza : w * z * a = a := by simp only [mul_assoc, ← hz, ← hw]
    have hzwb : z * w * b = b := by simp only [mul_assoc, ← hw, ← hz]
    exact {
      toFun := fun ⟨x, hL, hR⟩ ↦ ⟨z * x,
        ⟨IsGreenL.trans ⟨Or.inr ⟨z, rfl⟩, Or.inr ⟨w, by
          simpa [← mul_assoc] using (IsGreenR.cancellation hR hwza).symm⟩⟩
          (hL.trans h_L_ab), hz.symm ▸ IsGreenR.mul_left z hR⟩⟩
      invFun := fun ⟨y, hL, hR⟩ ↦ ⟨w * y,
        ⟨IsGreenL.trans ⟨Or.inr ⟨w, rfl⟩, Or.inr ⟨z, by
          simpa [← mul_assoc] using (IsGreenR.cancellation hR hzwb).symm⟩⟩
          (hL.trans h_L_ab.symm), hw.symm ▸ IsGreenR.mul_left w hR⟩⟩
      left_inv := fun ⟨x, _, hR⟩ ↦ Subtype.ext <| by
        simpa [← mul_assoc] using IsGreenR.cancellation hR hwza
      right_inv := fun ⟨y, _, hR⟩ ↦ Subtype.ext <| by
        simpa [← mul_assoc] using IsGreenR.cancellation hR hzwb
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
  Eq.trans (Fintype.card_congr (equivHClassOfIsGreenL hL))
    (Fintype.card_congr (equivHClassOfIsGreenR hR))

/-- If `a` and `b` are `J`-related in a finite semigroup, they are also `D`-related. -/
lemma isGreenD_of_isGreenJ [Finite S] {a b : S} (h : IsGreenJ a b) : IsGreenD a b := by
  cases h.left <;> cases h.right <;>
    grind [isGreenD_of_left_left, isGreenD_of_left_right,
        isGreenD_of_right_left, isGreenD_of_right_right,
        isGreenD_of_JRel_left_both, isGreenD_of_JRel_right_both,
        isGreenD_of_JRel_both, IsGreenD.refl, IsGreenD.symm]

/-- If `a` and `b` are `D`-related, they satisfy the basic `J`-relation step. -/
lemma isGreenJRel_of_isGreenD {a b : S} (h : IsGreenD a b) : IsGreenJRel a b :=
  let ⟨z, hL, hR⟩ := h
  match hL.left, hR.left with
  | .inl rfl, .inl rfl => .eq rfl
  | .inl rfl, .inr ⟨v, hv⟩ => .mul_right v hv
  | .inr ⟨u, hu⟩, .inl rfl => .mul_left u hu
  | .inr ⟨u, hu⟩, .inr ⟨v, hv⟩ => .mul_both u v (hu ▸ hv ▸ (mul_assoc u b v).symm)

/-- If `a` and `b` are `D`-related, they are also `J`-related. -/
lemma isGreenJ_of_isGreenD {a b : S} (h : IsGreenD a b) : IsGreenJ a b :=
  ⟨isGreenJRel_of_isGreenD h, isGreenJRel_of_isGreenD h.symm⟩

/-- In a finite semigroup, Green's `D` relation and Green's `J` relation are equal. -/
theorem isGreenD_eq_isGreenJ_of_finite [Finite S] : (IsGreenD : S → S → Prop) = IsGreenJ :=
  funext₂ fun _ _ => propext ⟨isGreenJ_of_isGreenD, isGreenD_of_isGreenJ⟩

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
      intro n
      induction n with
      | zero => exact IsGreenR.refl b
      | succ n ih => exact IsGreenR.trans hR_bz (IsGreenR.mul_left c ih)
    have h_b_eq_ckb : ∃ k > 0, b = leftMulSeq c b k := by
      obtain ⟨k, hk_pos, hk_eq_j⟩ : ∃ k > 0, i + k = j := ⟨j - i, by omega, by omega⟩
      have hs : ∀ m, leftMulSeq c b (i + m) = leftMulSeq c (leftMulSeq c b i) m := by
        intro m
        induction m with
        | zero => rfl
        | succ m ih =>
          rw [← add_assoc]
          exact congrArg (fun x ↦ c * x) ih
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
      · exact Or.inr ⟨leftMulSeq c c m_pred, by grind [leftMulSeq_mul_pull, leftMulSeq_pull_c]⟩
    · exact Or.inr ⟨leftMulSeq c w m, by grind [leftMulSeq_mul_pull, leftMulSeq_pull_c]⟩
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
    push Not at h
    obtain ⟨x₀, y₀, hx₀, hy₀, hxy₀⟩ := h
    have hx₀D : x₀ ∈ IsGreenD.eqvClass a := ⟨a, hx₀.left, IsGreenR.refl a⟩
    have hy₀D : y₀ ∈ IsGreenD.eqvClass a := ⟨a, hy₀.left, IsGreenR.refl a⟩
    have hxy₀D : x₀ * y₀ ∈ IsGreenD.eqvClass a := ⟨a, hxy₀.left, IsGreenR.refl a⟩
    have hD_ex : Exists (fun y ↦ IsGreenD.eqvClass a = IsGreenD.eqvClass y) := ⟨a, rfl⟩
    obtain ⟨_, e, heD, he_idem, hLx₀e, hRy₀e⟩ :=
      mul_mem_isGreenD_eqvClass_properties hD_ex x₀ y₀ hx₀D hy₀D hxy₀D
    have hLae : IsGreenL a e := IsGreenL.trans (IsGreenL.symm hx₀.left) hLx₀e
    have hRae : IsGreenR a e := IsGreenR.trans (IsGreenR.symm hy₀.right) hRy₀e
    have heH : e ∈ IsGreenH.eqvClass a := ⟨IsGreenL.symm hLae, IsGreenR.symm hRae⟩
    exact ⟨e, heH, he_idem, fun u v huH hvH ↦ by
      let hue : IsGreenH u e := huH.trans heH.symm
      let hve : IsGreenH v e := hvH.trans heH.symm
      have hLuv_v : IsGreenL (u * v) v := by
        simpa [MulSeq.mul_eq_self_of_isGreenH_idempotent hve he_idem]
          using IsGreenL.mul_right v hue.1
      have hRuv_u : IsGreenR (u * v) u := by
        simpa [MulSeq.mul_eq_self_of_isGreenH_idempotent hue he_idem]
          using IsGreenR.mul_left u hve.2
      exact ⟨hLuv_v.trans hvH.1, hRuv_u.trans huH.2⟩⟩
