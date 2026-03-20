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
    have he_idem : e * e = e := by
      dsimp [e]
      rw [← mul_assoc (x₀ * s) x₀ s, hs]
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
      rcases hR_ze.left with rfl | ⟨v, hv⟩
      · exact he_idem
      · rw [hv, ← mul_assoc e e v, he_idem]
    have hz_reg : ∃ u, z * u * z = z := by
      rcases hR_ze.right with rfl | ⟨u, hu⟩
      · exact ⟨e, by rw [he_idem, he_idem]⟩
      · use u
        rw [← hu, h_ez_z]
    obtain ⟨u, hu_z⟩ := hz_reg
    have hy_uz : y * u * z = y := by
      rcases hL_yz.left with rfl | ⟨p, hp⟩
      · exact hu_z
      · rw [hp, mul_assoc p z u, mul_assoc p (z * u) z, hu_z]
    rcases hL_yz.right with rfl | ⟨q, hq⟩
    · exact ⟨u, hy_uz⟩
    · use u * q
      rw [← mul_assoc y u q, mul_assoc (y * u) q y, ← hq, hy_uz]

/-- A bijection between the `H`-classes of two `L`-related elements. -/
noncomputable def equivHClassOfIsGreenL {a b : S} (h : IsGreenL a b) :
    IsGreenH.eqvClass a ≃ IsGreenH.eqvClass b := by
  by_cases hab_eq : a = b
  · exact hab_eq ▸ Equiv.refl _
  · have hex_w : ∃ w, a = w * b := h.left.resolve_left hab_eq
    let w := Classical.choose hex_w
    have hw : a = w * b := Classical.choose_spec hex_w
    have hba_neq : b ≠ a := fun heq ↦ hab_eq heq.symm
    have hex_z : ∃ z, b = z * a := h.right.resolve_left hba_neq
    let z := Classical.choose hex_z
    have hz : b = z * a := Classical.choose_spec hex_z
    have h_cancel_a : w * z * a = a := by rw [mul_assoc, ← hz, ← hw]
    have h_cancel_b : z * w * b = b := by rw [mul_assoc, ← hw, ← hz]
    refine {
      toFun := fun ⟨x, hx⟩ ↦ ⟨z * x, ?_⟩
      invFun := fun ⟨y, hy⟩ ↦ ⟨w * y, ?_⟩
      left_inv := fun ⟨x, hx⟩ ↦ Subtype.ext
        (by dsimp only; rw [← mul_assoc]; exact IsGreenR.cancellation hx.right h_cancel_a)
      right_inv := fun ⟨y, hy⟩ ↦ Subtype.ext
        (by dsimp only; rw [← mul_assoc]; exact IsGreenR.cancellation hy.right h_cancel_b)
    }
    · have hR1 : IsGreenR (z * x) (z * a) := IsGreenR.mul_left z hx.right
      have hR : IsGreenR (z * x) b := by rwa [← hz] at hR1
      have h_cancel_x : w * z * x = x := IsGreenR.cancellation hx.right h_cancel_a
      have hdvd1 : IsGreenLeftDvd (z * x) x := Or.inr ⟨z, rfl⟩
      have hdvd2 : IsGreenLeftDvd x (z * x) := Or.inr ⟨w, by rw [← mul_assoc, h_cancel_x]⟩
      have hL1 : IsGreenL (z * x) x := ⟨hdvd1, hdvd2⟩
      have hL : IsGreenL (z * x) b := IsGreenL.trans hL1 (IsGreenL.trans hx.left h)
      exact ⟨hL, hR⟩
    · have hR1 : IsGreenR (w * y) (w * b) := IsGreenR.mul_left w hy.right
      have hR : IsGreenR (w * y) a := by rwa [← hw] at hR1
      have h_cancel_y : z * w * y = y := IsGreenR.cancellation hy.right h_cancel_b
      have hdvd1 : IsGreenLeftDvd (w * y) y := Or.inr ⟨w, rfl⟩
      have hdvd2 : IsGreenLeftDvd y (w * y) := Or.inr ⟨z, by rw [← mul_assoc, h_cancel_y]⟩
      have hL1 : IsGreenL (w * y) y := ⟨hdvd1, hdvd2⟩
      have hL : IsGreenL (w * y) a := IsGreenL.trans hL1 (IsGreenL.trans hy.left (IsGreenL.symm h))
      exact ⟨hL, hR⟩

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
    Fintype.card (IsGreenH.eqvClass a) = Fintype.card (IsGreenH.eqvClass b) := by
  rcases h with ⟨z, hL, hR⟩
  let equiv_az := equivHClassOfIsGreenL hL
  let equiv_zb := equivHClassOfIsGreenR hR
  trans Fintype.card (IsGreenH.eqvClass z)
  · exact Fintype.card_congr equiv_az
  · exact Fintype.card_congr equiv_zb

/-- If `a` and `b` are `J`-related in a finite semigroup, they are also `D`-related. -/
lemma isGreenD_of_isGreenJ [Finite S] {a b : S} (h : IsGreenJ a b) : IsGreenD a b := by
  rcases h with ⟨hab, hba⟩
  cases hab
  case eq h1 => exact h1 ▸ IsGreenD.refl b
  case mul_left u h1 =>
    cases hba
    case eq h2 => exact h2.symm ▸ IsGreenD.refl a
    case mul_left x h2 => exact isGreenD_of_left_left h1 h2
    case mul_right y h2 => exact isGreenD_of_left_right h1 h2
    case mul_both x y h2 => exact isGreenD_of_JRel_left_both h1 h2
  case mul_right v h1 =>
    cases hba
    case eq h2 => exact h2.symm ▸ IsGreenD.refl a
    case mul_left x h2 => exact isGreenD_of_right_left h1 h2
    case mul_right y h2 => exact isGreenD_of_right_right h1 h2
    case mul_both x y h2 => exact isGreenD_of_JRel_right_both h1 h2
  case mul_both z u h1 =>
    cases hba
    case eq h2 => exact h2.symm ▸ IsGreenD.refl a
    case mul_left x h2 => exact IsGreenD.symm (isGreenD_of_JRel_left_both h2 h1)
    case mul_right y h2 => exact IsGreenD.symm (isGreenD_of_JRel_right_both h2 h1)
    case mul_both x y h2 => exact isGreenD_of_JRel_both h1 h2

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
lemma isGreenJ_of_isGreenD {a b : S} (h : IsGreenD a b) : IsGreenJ a b := by
  constructor
  · exact isGreenJRel_of_isGreenD h
  · have h_symm : IsGreenD b a := IsGreenD.symm h
    exact isGreenJRel_of_isGreenD h_symm

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
    have h_exists_c : ∃ c, z = c * b ∧ IsGreenLeftDvd c a := by
      rcases hL_zab.left with rfl | ⟨w, hw⟩
      · exact ⟨a, rfl, Or.inl rfl⟩
      · exact ⟨w * a, by rw [hw, ← mul_assoc], Or.inr ⟨w, rfl⟩⟩
    rcases h_exists_c with ⟨c, rfl, hc_dvd⟩
    rcases leftMulSeq_pigeonhole c b with ⟨i, j, hij, heq⟩
    have hR_all : ∀ n, IsGreenR b (leftMulSeq c b n) := by
      intro n
      induction n with
      | zero => exact IsGreenR.refl b
      | succ n ih => exact IsGreenR.trans hR_bz (IsGreenR.mul_left c ih)
    have hR_cib : IsGreenR b (leftMulSeq c b i) := hR_all i
    have h_b_eq_ckb : ∃ k > 0, b = leftMulSeq c b k := by
      let k := j - i
      have hk_pos : 0 < k := Nat.sub_pos_of_lt hij
      have hk_eq_j : i + k = j := Nat.add_sub_of_le (le_of_lt hij)
      have h_shift : leftMulSeq c b j = leftMulSeq c (leftMulSeq c b i) k := by
        have hs : ∀ m, leftMulSeq c b (i + m) = leftMulSeq c (leftMulSeq c b i) m := by
          intro m
          induction m with
          | zero => rfl
          | succ m ih =>
            calc leftMulSeq c b (i + m + 1) = c * leftMulSeq c b (i + m) := rfl
              _ = c * leftMulSeq c (leftMulSeq c b i) m := by rw [ih]
              _ = leftMulSeq c (leftMulSeq c b i) (m + 1) := rfl
        calc leftMulSeq c b j = leftMulSeq c b (i + k) := by rw [← hk_eq_j]
          _ = leftMulSeq c (leftMulSeq c b i) k := hs k
      have h_gi_k : leftMulSeq c (leftMulSeq c b i) k = leftMulSeq c b i := by
        rw [← h_shift, heq]
      use k, hk_pos
      rcases hR_cib.left with heq_b | ⟨v_outer, hv⟩
      · calc b = leftMulSeq c b i := heq_b
          _ = leftMulSeq c (leftMulSeq c b i) k := h_gi_k.symm
          _ = leftMulSeq c b k := by rw [← heq_b]
      · calc b = leftMulSeq c b i * v_outer := hv
          _ = leftMulSeq c (leftMulSeq c b i) k * v_outer := by rw [h_gi_k]
          _ = leftMulSeq c (leftMulSeq c b i * v_outer) k :=
            (leftMulSeq_mul_pull c k _ v_outer).symm
          _ = leftMulSeq c b k := by rw [← hv]
    rcases h_b_eq_ckb with ⟨k, hk_pos, hk_eq⟩
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hk_pos)
    rcases hc_dvd with hc_eq_a | ⟨w, hw⟩
    · rcases m with _ | m_pred
      · have h_final : b = a * b := by
          calc b = leftMulSeq c b (0 + 1) := hk_eq
            _ = leftMulSeq c (c * b) 0 := leftMulSeq_pull_c c 0 b
            _ = leftMulSeq c (a * b) 0 := congrArg (fun x ↦ leftMulSeq c (x * b) 0) hc_eq_a
            _ = a * b := rfl
        exact Or.inl h_final
      · have h_final : b = leftMulSeq c c m_pred * (a * b) := by
          calc b = leftMulSeq c b (m_pred + 1 + 1) := hk_eq
            _ = leftMulSeq c (c * b) (m_pred + 1) := leftMulSeq_pull_c c (m_pred + 1) b
            _ = leftMulSeq c (a * b) (m_pred + 1) :=
              congrArg (fun x ↦ leftMulSeq c (x * b) (m_pred + 1)) hc_eq_a
            _ = leftMulSeq c (c * (a * b)) m_pred := leftMulSeq_pull_c c m_pred (a * b)
            _ = leftMulSeq c c m_pred * (a * b) := leftMulSeq_mul_pull c m_pred c (a * b)
        exact Or.inr ⟨leftMulSeq c c m_pred, h_final⟩
    · have h_final : b = leftMulSeq c w m * (a * b) := by
        calc b = leftMulSeq c b (m + 1) := hk_eq
          _ = leftMulSeq c (c * b) m := leftMulSeq_pull_c c m b
          _ = leftMulSeq c ((w * a) * b) m := congrArg (fun x ↦ leftMulSeq c (x * b) m) hw
          _ = leftMulSeq c (w * (a * b)) m := congrArg (leftMulSeq c · m) (mul_assoc w a b)
          _ = leftMulSeq c w m * (a * b) := leftMulSeq_mul_pull c m w (a * b)
      exact Or.inr ⟨leftMulSeq c w m, h_final⟩
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
  [Finite S] {D : Set S} (hD : ∃ x, D = IsGreenD.eqvClass x)
    (a b : S) (ha : a ∈ D) (hb : b ∈ D) (hab : a * b ∈ D) :
    (IsGreenR a (a * b) ∧ IsGreenL b (a * b)) ∧
    (∃ e ∈ D, e * e = e ∧ IsGreenL a e ∧ IsGreenR b e) := by
  obtain ⟨x0, hx0⟩ := hD
  have hDa : IsGreenD a x0 := by have h := ha; rw [hx0] at h; exact h
  have hDb : IsGreenD b x0 := by have h := hb; rw [hx0] at h; exact h
  have hDab : IsGreenD (a * b) x0 := by have h := hab; rw [hx0] at h; exact h
  have h_a_D_ab : IsGreenD a (a * b) := IsGreenD.trans hDa (IsGreenD.symm hDab)
  have h_b_D_ab : IsGreenD b (a * b) := IsGreenD.trans hDb (IsGreenD.symm hDab)
  have hR_a_ab : IsGreenR a (a * b) := isGreenR_sr_of_isGreenD_sr h_a_D_ab
  have hL_b_ab : IsGreenL b (a * b) := isGreenL_sl_of_isGreenD_sl h_b_D_ab
  refine ⟨⟨hR_a_ab, hL_b_ab⟩, ?_⟩
  have h_a_dvd : IsGreenRightDvd a (a * b) := hR_a_ab.left
  have h_b_dvd : IsGreenLeftDvd b (a * b) := hL_b_ab.left
  rcases h_a_dvd with h_a_eq | ⟨u, hu⟩
  · rcases h_b_dvd with h_b_eq | ⟨v, hv⟩
    · use a
      have hab_eq : a = b := h_a_eq.trans h_b_eq.symm
      have idem : a * a = a := by
        calc a * a = a * b := congrArg (fun x ↦ a * x) hab_eq
             _     = a     := h_a_eq.symm
      refine ⟨ha, idem, IsGreenL.refl a, ?_⟩
      exact hab_eq ▸ IsGreenR.refl b
    · use b
      have h1 : v * a = b := by
        calc v * a = v * (a * b) := congrArg (fun x ↦ v * x) h_a_eq
             _     = b           := hv.symm
      have idem : b * b = b := by
        calc b * b = (v * a) * b := congrArg (fun x ↦ x * b) h1.symm
             _     = v * (a * b) := mul_assoc v a b
             _     = b           := hv.symm
      have hLab : IsGreenL a b := ⟨Or.inr ⟨a, h_a_eq⟩, Or.inr ⟨v, h1.symm⟩⟩
      exact ⟨hb, idem, hLab, IsGreenR.refl b⟩
  · rcases h_b_dvd with h_b_eq | ⟨v, hv⟩
    · use a
      have h2 : b * u = a := by
        calc b * u = (a * b) * u := congrArg (fun x ↦ x * u) h_b_eq
             _     = a           := hu.symm
      have idem : a * a = a := by
        calc a * a = a * (b * u) := congrArg (fun x ↦ a * x) h2.symm
             _     = (a * b) * u := (mul_assoc a b u).symm
             _     = a           := hu.symm
      have hRba : IsGreenR b a := ⟨Or.inr ⟨b, h_b_eq⟩, Or.inr ⟨u, h2.symm⟩⟩
      exact ⟨ha, idem, IsGreenL.refl a, hRba⟩
    · use v * a
      have he_eq : v * a = b * u := by
        calc v * a = v * (a * b * u)   := congrArg (fun x ↦ v * x) hu
             _     = (v * (a * b)) * u := (mul_assoc v (a * b) u).symm
             _     = b * u             := congrArg (fun x ↦ x * u) hv.symm
      have idem : (v * a) * (v * a) = v * a := by
        calc (v * a) * (v * a) = (v * a) * (b * u) := congrArg (fun x ↦ (v * a) * x) he_eq
             _ = v * (a * (b * u))                 := mul_assoc v a (b * u)
             _ = v * (a * b * u)                   :=
             congrArg (fun x ↦ v * x) (mul_assoc a b u).symm
             _ = v * a                             := congrArg (fun x ↦ v * x) hu.symm
      have hLae1 : a = a * (v * a) := by
        calc a = a * b * u   := hu
             _ = a * (b * u) := mul_assoc a b u
             _ = a * (v * a) := congrArg (fun x ↦ a * x) he_eq.symm
      have hLae : IsGreenL a (v * a) := ⟨Or.inr ⟨a, hLae1⟩, Or.inr ⟨v, rfl⟩⟩
      have hRbe1 : b = (v * a) * b := by
        calc b = v * (a * b) := hv
             _ = (v * a) * b := (mul_assoc v a b).symm
      have hRbe : IsGreenR b (v * a) := ⟨Or.inr ⟨b, hRbe1⟩, Or.inr ⟨u, he_eq⟩⟩
      have heD : v * a ∈ D := by
        have hDea : IsGreenD (v * a) a := ⟨a, IsGreenL.symm hLae, IsGreenR.refl a⟩
        have he_D : IsGreenD (v * a) x0 := IsGreenD.trans hDea hDa
        rw [hx0]
        exact he_D
      exact ⟨heD, idem, hLae, hRbe⟩

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
    have hx₀D : x₀ ∈ IsGreenD.eqvClass a := by
      simp only [IsGreenD.eqvClass, Set.mem_setOf_eq]
      exact ⟨a, hx₀H.left, IsGreenR.refl a⟩
    have hy₀D : y₀ ∈ IsGreenD.eqvClass a := by
      simp only [IsGreenD.eqvClass, Set.mem_setOf_eq]
      exact ⟨a, hy₀H.left, IsGreenR.refl a⟩
    have hxy₀D : x₀ * y₀ ∈ IsGreenD.eqvClass a := by
      simp only [IsGreenD.eqvClass, Set.mem_setOf_eq]
      exact ⟨a, hxy₀H.left, IsGreenR.refl a⟩
    obtain ⟨_, e, heD, he_idem, hLx₀e, hRy₀e⟩ :=
      mul_mem_isGreenD_eqvClass_properties (D := IsGreenD.eqvClass a) ⟨a, rfl⟩ x₀ y₀ hx₀D hy₀D hxy₀D
    have hLx₀a : IsGreenL x₀ a := hx₀H.left
    have hRy₀a : IsGreenR y₀ a := hy₀H.right
    have hLae : IsGreenL a e := IsGreenL.trans (IsGreenL.symm hLx₀a) hLx₀e
    have hRae : IsGreenR a e := IsGreenR.trans (IsGreenR.symm hRy₀a) hRy₀e
    have heH : e ∈ IsGreenH.eqvClass a := ⟨IsGreenL.symm hLae, IsGreenR.symm hRae⟩
    refine ⟨e, heH, he_idem, ?_⟩
    intro u v huH hvH
    have hue : IsGreenH u e := IsGreenH.trans huH (IsGreenH.symm heH)
    have hve : IsGreenH v e := IsGreenH.trans hvH (IsGreenH.symm heH)
    have hLue : IsGreenL u e := hue.left
    have hRve : IsGreenR v e := hve.right
    have hev : e * v = v := by
      rcases hRve.left with rfl | ⟨z, hz⟩
      · exact he_idem
      · rw [hz, ← mul_assoc, he_idem]
    have hue_eq : u * e = u := by
      rcases hLue.left with rfl | ⟨w, hw⟩
      · exact he_idem
      · rw [hw, mul_assoc, he_idem]
    have hLuv_ev : IsGreenL (u * v) (e * v) := IsGreenL.mul_right v hLue
    have hLuv_v : IsGreenL (u * v) v := by rwa [hev] at hLuv_ev
    have hRuv_ue : IsGreenR (u * v) (u * e) := IsGreenR.mul_left u hRve
    have hRuv_u : IsGreenR (u * v) u := by rwa [hue_eq] at hRuv_ue
    have hLuv_a : IsGreenL (u * v) a := IsGreenL.trans hLuv_v hvH.left
    have hRuv_a : IsGreenR (u * v) a := IsGreenR.trans hRuv_u huH.right
    exact ⟨hLuv_a, hRuv_a⟩
