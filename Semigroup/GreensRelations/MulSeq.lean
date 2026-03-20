/- Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz -/

import Semigroup.GreensRelations.Classes
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Multiplication Sequences and Helper Lemmas

This file provides tools for analyzing finite semigroups using iterated multiplication
sequences (`leftMulSeq`, `rightMulSeq`). It contains intermediate structural lemmas
required to prove the main theorems of Green's relations.

## Main definitions

* `MulSeq.rightMulSeq a c n`: The element obtained by multiplying `a` by `c` on the right `n` times.
* `MulSeq.leftMulSeq c a n`: The element obtained by multiplying `a` by `c` on the left `n` times.

## Main results

* `leftMulSeq_pigeonhole`: Proof that in a finite semigroup, a left multiplication sequence
  eventually repeats.
* `greenL_of_eq_mul_mul`: If `b = c * b * d`, then `b` is Green's L-related to `c * b`.
* `isGreenD_of_JRel_both`: Proof that the basic J-relation (two-sided divisibility)
  implies the D-relation in finite semigroups.
* `exists_idempotent_in_greenL_of_regular`: Every regular element has an idempotent in its L-class.

## References

* [T. Colombet, *The Factorization Forest Theorem*][colombet2008]

## Tags

multiplication sequence, finite semigroup, regular element, idempotent, pigeonhole principle
-/

variable {S : Type*} [Semigroup S]

/-- The opposite semigroup construction gives an equivalence between `S` and `Sᵐᵒᵖ`
  that preserves Green's relations, so finiteness of `S` implies finiteness of `Sᵐᵒᵖ`. -/
instance instFiniteMulOpposite [Finite S] : Finite Sᵐᵒᵖ :=
  Finite.of_equiv S MulOpposite.opEquiv

namespace MulSeq

/-- The sequence defined by repeatedly multiplying `a` by `c` on the right. -/
def rightMulSeq (a c : S) : ℕ → S
  | 0 => a
  | n + 1 => rightMulSeq a c n * c

/-- Left multiplication can be pulled out of a `rightMulSeq`. -/
lemma rightMulSeq_mul_pull (c : S) (m : ℕ) (x u : S) :
    rightMulSeq (u * x) c m = u * rightMulSeq x c m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    calc rightMulSeq (u * x) c (m + 1) = rightMulSeq (u * x) c m * c := rfl
      _ = (u * rightMulSeq x c m) * c := by rw [ih]
      _ = u * (rightMulSeq x c m * c) := mul_assoc u (rightMulSeq x c m) c
      _ = u * rightMulSeq x c (m + 1) := rfl

/-- Extracting a right multiplication from the base of a `rightMulSeq`. -/
lemma rightMulSeq_pull_c (c : S) (n : ℕ) (x : S) :
    rightMulSeq x c (n + 1) = rightMulSeq (x * c) c n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc rightMulSeq x c (n + 1 + 1) = rightMulSeq x c (n + 1) * c := rfl
      _ = rightMulSeq (x * c) c n * c := by rw [ih]
      _ = rightMulSeq (x * c) c (n + 1) := rfl

/-- The sequence defined by repeatedly multiplying `a` by `c` on the left. -/
def leftMulSeq (c a : S) : ℕ → S
  | 0 => a
  | n + 1 => c * leftMulSeq c a n

/-- Right multiplication can be pulled out of a `leftMulSeq`. -/
lemma leftMulSeq_mul_pull (c : S) (m : ℕ) (x v : S) :
    leftMulSeq c (x * v) m = leftMulSeq c x m * v := by
  induction m with
  | zero => rfl
  | succ m ih =>
    calc leftMulSeq c (x * v) (m + 1) = c * leftMulSeq c (x * v) m := rfl
      _ = c * (leftMulSeq c x m * v) := by rw [ih]
      _ = (c * leftMulSeq c x m) * v := (mul_assoc c (leftMulSeq c x m) v).symm
      _ = leftMulSeq c x (m + 1) * v := rfl

/-- Extracting a left multiplication from the base of a `leftMulSeq`. -/
lemma leftMulSeq_pull_c (c : S) (n : ℕ) (x : S) :
    leftMulSeq c x (n + 1) = leftMulSeq c (c * x) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc leftMulSeq c x (n + 1 + 1) = c * leftMulSeq c x (n + 1) := rfl
      _ = c * leftMulSeq c (c * x) n := by rw [ih]
      _ = leftMulSeq c (c * x) (n + 1) := rfl

/-- In a finite semigroup, a `leftMulSeq` eventually repeats. -/
lemma leftMulSeq_pigeonhole [Finite S] (c a : S) :
    ∃ i j : ℕ, i < j ∧ leftMulSeq c a i = leftMulSeq c a j := by
  obtain ⟨i, j, h_neq, heq⟩ := Finite.exists_ne_map_eq_of_infinite (leftMulSeq c a)
  rcases lt_trichotomy i j with h_lt | h_eq | h_gt
  · exact ⟨i, j, h_lt, heq⟩
  · exact False.elim (h_neq h_eq)
  · exact ⟨j, i, h_gt, heq.symm⟩

/-- Any element in a `leftMulSeq` starting from `a` is a left multiple of `a`. -/
lemma leftMulSeq_isGreenLeftDvd (c a : S) (m : ℕ) :
    IsGreenLeftDvd (leftMulSeq c a m) a := by
  cases m with
  | zero => exact Or.inl rfl
  | succ m =>
    induction m with
    | zero => exact Or.inr ⟨c, rfl⟩
    | succ m ih =>
      rcases ih with h_eq | ⟨w, hw⟩
      · exact Or.inr ⟨c, by rw [leftMulSeq, h_eq]⟩
      · exact Or.inr ⟨c * w, by rw [leftMulSeq, hw, ← mul_assoc]⟩

/-- Left divisibility is preserved by left multiplication. -/
lemma isGreenLeftDvd_mul_left (a b x : S) (h : IsGreenLeftDvd a b) :
    IsGreenLeftDvd (x * a) b := by
  rcases h with rfl | ⟨w, hw⟩
  · exact Or.inr ⟨x, rfl⟩
  · exact Or.inr ⟨x * w, by rw [hw, ← mul_assoc]⟩

/-- Left and right multiplication sequences commute. -/
lemma leftMulSeq_rightMulSeq_comm (c x d : S) (i k : ℕ) :
    leftMulSeq c (rightMulSeq x d k) i = rightMulSeq (leftMulSeq c x i) d k := by
  induction i with
  | zero => rfl
  | succ i ih =>
    calc leftMulSeq c (rightMulSeq x d k) (i + 1) = c * leftMulSeq c (rightMulSeq x d k) i := rfl
      _ = c * rightMulSeq (leftMulSeq c x i) d k := by rw [ih]
      _ = rightMulSeq (c * leftMulSeq c x i) d k :=
        (rightMulSeq_mul_pull d k (leftMulSeq c x i) c).symm
      _ = rightMulSeq (leftMulSeq c x (i + 1)) d k := rfl

/-- If `b = c * b * d`, applying `n` left steps then `n` right steps yields `b`. -/
lemma b_eq_right_left_seq (c b d : S) (h : b = c * b * d) (n : ℕ) :
    b = rightMulSeq (leftMulSeq c b n) d n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc b = c * b * d := h
      _ = c * rightMulSeq (leftMulSeq c b n) d n * d := congrArg (fun x ↦ c * x * d) ih
      _ = c * (rightMulSeq (leftMulSeq c b n) d n * d) :=
        mul_assoc c (rightMulSeq (leftMulSeq c b n) d n) d
      _ = c * rightMulSeq (leftMulSeq c b n) d (n + 1) := rfl
      _ = rightMulSeq (c * leftMulSeq c b n) d (n + 1) :=
        (rightMulSeq_mul_pull d (n + 1) (leftMulSeq c b n) c).symm
      _ = rightMulSeq (leftMulSeq c b (n + 1)) d (n + 1) := rfl

/-- If `b = c * b * d` in a finite semigroup, `b` is equivalent to some left multiple sequence. -/
lemma eq_leftMulSeq_of_eq_mul_mul [Finite S] {b c d : S} (h : b = c * b * d) :
    ∃ k > 0, b = leftMulSeq c b k := by
  rcases leftMulSeq_pigeonhole c b with ⟨i, j, hij, heq⟩
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
  have h_fi_k : leftMulSeq c (leftMulSeq c b i) k = leftMulSeq c b i := by
    rw [← h_shift, heq]
  have h_b_eq : b = rightMulSeq (leftMulSeq c b i) d i := b_eq_right_left_seq c b d h i
  have h_b_eq_k : b = leftMulSeq c b k := by
    calc b = rightMulSeq (leftMulSeq c b i) d i := h_b_eq
      _ = rightMulSeq (leftMulSeq c (leftMulSeq c b i) k) d i := by rw [h_fi_k]
      _ = leftMulSeq c (rightMulSeq (leftMulSeq c b i) d i) k :=
        (leftMulSeq_rightMulSeq_comm c (leftMulSeq c b i) d k i).symm
      _ = leftMulSeq c b k := by rw [← h_b_eq]
  exact ⟨k, hk_pos, h_b_eq_k⟩

/-- If `b = c * b * d`, then `b` is L-related to `c * b`. -/
lemma greenL_of_eq_mul_mul [Finite S] {b c d : S} (h : b = c * b * d) : IsGreenL b (c * b) := by
  obtain ⟨k, hk_pos, hk_eq⟩ := eq_leftMulSeq_of_eq_mul_mul h
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hk_pos)
  have h_cb_b : IsGreenLeftDvd (c * b) b := Or.inr ⟨c, rfl⟩
  have h_b_cb : IsGreenLeftDvd b (c * b) := by
    have h_eq_b : b = leftMulSeq c (c * b) m := by
      calc b = leftMulSeq c b (m + 1) := hk_eq
        _ = leftMulSeq c (c * b) m := leftMulSeq_pull_c c m b
    have h_left := leftMulSeq_isGreenLeftDvd c (c * b) m
    rcases h_left with h_eq_l | ⟨w, hw⟩
    · exact Or.inl (h_eq_b.trans h_eq_l)
    · exact Or.inr ⟨w, h_eq_b.trans hw⟩
  exact ⟨h_b_cb, h_cb_b⟩

open MulOpposite in
/-- If `b = c * b * d`, then `b` is R-related to `b * d`. -/
lemma greenR_of_eq_mul_mul [Finite S] {b c d : S} (h : b = c * b * d) : IsGreenR b (b * d) := by
  grind [op_mul, mul_assoc, isGreenR_iff_isGreenL_op, greenL_of_eq_mul_mul]

/-- Green's L relation holds when a left multiplier is dropped from an already L-related element. -/
lemma isGreenL_of_isGreenL_mul {b x z : S} (h : IsGreenL b (x * (z * b))) : IsGreenL b (z * b) := by
  have h2 : IsGreenLeftDvd (z * b) b := Or.inr ⟨z, rfl⟩
  have h1 : IsGreenLeftDvd b (z * b) := by
    cases h.left with
    | inl h_eq => exact Or.inr ⟨x, h_eq⟩
    | inr h_ex =>
      rcases h_ex with ⟨w, hw⟩
      exact Or.inr ⟨w * x, by
        calc b = w * (x * (z * b)) := hw
          _ = (w * x) * (z * b) := (mul_assoc w x (z * b)).symm⟩
  exact ⟨h1, h2⟩

open MulOpposite in
/-- Green's R relation holds when a right multiplier
  is dropped from an already R-related element. -/
lemma isGreenR_of_isGreenR_mul {b u y : S} (h : IsGreenR b ((b * u) * y)) : IsGreenR b (b * u) := by
  grind [op_mul, mul_assoc, isGreenR_iff_isGreenL_op, isGreenL_of_isGreenL_mul]

/-- If `b = x * z * b * d`, then `b` is L-related to `z * b`. -/
lemma isGreenL_of_eq_mul_mul_mul [Finite S] {b x z d : S} (h : b = (x * z) * b * d) :
    IsGreenL b (z * b) := by
  apply isGreenL_of_isGreenL_mul (x := x)
  rw [← mul_assoc]
  exact greenL_of_eq_mul_mul h

open MulOpposite in
/-- If `b = c * b * (u * y)`, then `b` is R-related to `b * u`. -/
lemma isGreenR_of_eq_mul_mul_mul [Finite S] {b c u y : S} (h : b = c * b * (u * y)) :
    IsGreenR b (b * u) := by
  grind [op_mul, mul_assoc, isGreenR_iff_isGreenL_op, isGreenL_of_eq_mul_mul_mul]

/-- If `a` is a two-sided multiple of `b`, and `b` is a two-sided multiple of `a`,
then `a` and `b` are Green's D-related. -/
lemma isGreenD_of_JRel_both [Finite S] {a b x y z u : S}
    (h1 : a = z * b * u) (h2 : b = x * a * y) : IsGreenD a b := by
  have h_b_eq : b = (x * z) * b * (u * y) := by
    calc b = x * a * y := h2
      _ = x * (z * b * u) * y := by rw [h1]
      _ = x * ((z * b) * u) * y := rfl
      _ = (x * (z * b)) * u * y := by rw [← mul_assoc x (z * b) u]
      _ = ((x * z) * b) * u * y := by rw [← mul_assoc x z b]
      _ = ((x * z) * b) * (u * y) := by rw [mul_assoc ((x * z) * b) u y]
  have hR : IsGreenR b (b * u) := isGreenR_of_eq_mul_mul_mul h_b_eq
  have hL : IsGreenL b (z * b) := isGreenL_of_eq_mul_mul_mul h_b_eq
  have hL_bu_a : IsGreenL (b * u) a := by
    have hL_bu_zbu : IsGreenL (b * u) ((z * b) * u) := IsGreenL.mul_right u hL
    exact h1.symm ▸ hL_bu_zbu
  exact ⟨b * u, IsGreenL.symm hL_bu_a, IsGreenR.symm hR⟩

/-- If `a` is a left multiple of `b` and `b` is a two-sided multiple of `a`, they are D-related. -/
lemma isGreenD_of_JRel_left_both [Finite S] {a b x y z : S}
    (h1 : a = z * b) (h2 : b = x * a * y) : IsGreenD a b := by
  have h_b_eq : b = (x * z) * b * y := by
    calc b = x * a * y := h2
      _ = x * (z * b) * y := by rw [h1]
      _ = (x * z) * b * y := by rw [← mul_assoc x z b]
  have hR : IsGreenR b (b * y) := greenR_of_eq_mul_mul h_b_eq
  have hl1 := greenL_of_eq_mul_mul h_b_eq
  have h_assoc : (x * z) * b = x * (z * b) := mul_assoc x z b
  have hL : IsGreenL b (x * (z * b)) := h_assoc ▸ hl1
  have hL2 : IsGreenL b (z * b) := isGreenL_of_isGreenL_mul hL
  have hL3 : IsGreenL b a := h1.symm ▸ hL2
  exact ⟨b, IsGreenL.symm hL3, IsGreenR.refl b⟩

open MulOpposite in
/-- If `a` is a right multiple of `b` and `b` is a two-sided multiple of `a`, they are D-related. -/
lemma isGreenD_of_JRel_right_both [Finite S] {a b x y u : S}
    (h1 : a = b * u) (h2 : b = x * a * y) : IsGreenD a b := by
  grind [op_mul, mul_assoc, IsGreenD.isGreenD_iff_isGreenD_op, isGreenD_of_JRel_left_both]

/-- If `a` is a left multiple of `b` and `b` is a right multiple of `a`, they are D-related. -/
lemma isGreenD_of_left_right [Finite S] {a b u y : S} (h1 : a = u * b) (h2 : b = a * y) :
  IsGreenD a b := by
  have h_a : a = u * a * y := by
    calc a = u * b := h1
      _ = u * (a * y) := congrArg (fun x ↦ u * x) h2
      _ = (u * a) * y := (mul_assoc u a y).symm
  have hR : IsGreenR a (a * y) := greenR_of_eq_mul_mul h_a
  have hR_ab : IsGreenR a b := h2.symm ▸ hR
  exact ⟨a, IsGreenL.refl a, hR_ab⟩

/-- If `a` is a right multiple of `b` and `b` is a left multiple of `a`, they are D-related. -/
lemma isGreenD_of_right_left [Finite S] {a b v x : S} (h1 : a = b * v) (h2 : b = x * a) :
  IsGreenD a b := by
  have h_a : a = x * a * v := by
    calc a = b * v := h1
      _ = (x * a) * v := congrArg (fun y ↦ y * v) h2
  have hL : IsGreenL a (x * a) := greenL_of_eq_mul_mul h_a
  have hL_ab : IsGreenL a b := h2.symm ▸ hL
  exact ⟨b, hL_ab, IsGreenR.refl b⟩

/-- If `a` is a left multiple of `b` and `b` is a left multiple of `a`, they are D-related. -/
lemma isGreenD_of_left_left [Finite S] {a b u x : S} (h1 : a = u * b) (h2 : b = x * a) :
  IsGreenD a b := by
  exact ⟨b, ⟨Or.inr ⟨u, h1⟩, Or.inr ⟨x, h2⟩⟩, IsGreenR.refl b⟩

/-- If `a` is a right multiple of `b` and `b` is a right multiple of `a`, they are D-related. -/
lemma isGreenD_of_right_right [Finite S] {a b v y : S} (h1 : a = b * v) (h2 : b = a * y) :
  IsGreenD a b := by
  exact ⟨a, IsGreenL.refl a, ⟨Or.inr ⟨v, h1⟩, Or.inr ⟨y, h2⟩⟩⟩

/-- A regular element `a` has an idempotent in its L-class. -/
lemma exists_idempotent_in_greenL_of_regular {S : Type*} [Semigroup S] {a : S}
    (hReg : IsGreenRegular a) : ∃ e ∈ IsGreenL.eqvClass a, e * e = e := by
  obtain ⟨s, hs⟩ := hReg
  use s * a
  constructor
  · constructor
    · right; use s
    · right; use a
      rw [← mul_assoc]
      exact hs.symm
  · have h_assoc : (s * a) * (s * a) = s * (a * s * a) := by simp [mul_assoc]
    rw [h_assoc, hs]

open MulOpposite in
/-- A regular element `a` has an idempotent in its R-class. -/
lemma exists_idempotent_in_greenR_of_regular {S : Type*} [Semigroup S] {a : S}
    (hReg : IsGreenRegular a) : ∃ e ∈ IsGreenR.eqvClass a, e * e = e := by
  have hReg_op : IsGreenRegular (op a) := by
    obtain ⟨s, hs⟩ := hReg
    use op s
    simp only [← op_mul, ← mul_assoc, hs]
  obtain ⟨e_op, he_L, he_idem⟩ := exists_idempotent_in_greenL_of_regular hReg_op
  use unop e_op
  constructor
  · have h_L_op : IsGreenL (op (unop e_op)) (op a) := by rwa [op_unop]
    exact isGreenR_iff_isGreenL_op.mpr h_L_op
  · exact op_injective (by simp only [op_mul, op_unop, he_idem])

/-- Two H-related idempotents must be equal. -/
lemma eq_of_isGreenH_of_idempotent {S : Type*} [Semigroup S] {a b : S}
    (hab : IsGreenH a b) (ha : a * a = a) (hb : b * b = b) : a = b := by
  have h1 : a * b = b := by
    rcases hab.right.right with rfl | ⟨x, rfl⟩ <;> simp [← mul_assoc, ha]
  have h2 : a * b = a := by
    rcases hab.left.left with rfl | ⟨y, rfl⟩ <;> simp [mul_assoc, ha, hb]
  rw [← h2, h1]

/-- If `a` is H-related to an idempotent `e`, multiplying `a` by `e` leaves `a` unchanged. -/
lemma mul_eq_self_of_isGreenH_idempotent {S : Type*} [Semigroup S] {a e : S}
    (hae : IsGreenH a e) (he : e * e = e) : a * e = a ∧ e * a = a := by
  constructor
  · rcases hae.left.left with rfl | ⟨w, rfl⟩ <;> simp [mul_assoc, he]
  · rcases hae.right.left with rfl | ⟨w, rfl⟩ <;> simp [← mul_assoc, he]

end MulSeq
