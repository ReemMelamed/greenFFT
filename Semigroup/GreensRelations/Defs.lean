/- Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz -/

import Mathlib.Algebra.Group.Basic

/-!
# Green's Relations Definitions

This file contains the fundamental definitions of Green's relations (L, R, H, D, and J)
on a general semigroup.

## Main definitions

* `IsGreenLeftDvd`: Left divisibility in a semigroup.
* `IsGreenRightDvd`: Right divisibility in a semigroup.
* `IsGreenJRel`: The basic step of being a two-sided multiple.
* `IsGreenL`: Green's L relation (generating the same left ideal).
* `IsGreenR`: Green's R relation (generating the same right ideal).
* `IsGreenH`: Green's H relation (the intersection of L and R).
* `IsGreenD`: Green's D relation (the composition of L and R).
* `IsGreenJ`: Green's J relation (generating the same two-sided ideal).

## References

* [T. Colcombet, *The Factorization Forest Theorem*][colcombet2008]
-/

variable {S : Type*} [Semigroup S]

/-- `IsGreenLeftDvd a b` means that `a` is a left multiple of `b`,
  i.e., `a = b` or `a = z * b`. -/
def IsGreenLeftDvd (a b : S) : Prop := a = b ∨ ∃ z, a = z * b

/-- `IsGreenRightDvd a b` means that `a` is a right multiple of `b`,
  i.e., `a = b` or `a = b * z`. -/
def IsGreenRightDvd (a b : S) : Prop := a = b ∨ ∃ z, a = b * z

/-- `IsGreenJRel a b` represents the basic step of being a two-sided multiple.
  `a` is related to `b` if `a = b`, `a = u * b`, `a = b * v`, or `a = u * b * v`. -/
inductive IsGreenJRel (a b : S) : Prop
  /-- `a` and `b` are equal. -/
  | of_eq (h : a = b)
  /-- `a` is a left multiple of `b`. -/
  | mul_left (u : S) (h : a = u * b)
  /-- `a` is a right multiple of `b`. -/
  | mul_right (v : S) (h : a = b * v)
  /-- `a` is a two-sided multiple of `b`. -/
  | mul_both (u v : S) (h : a = u * b * v)

/-- Green's L relation: `a` and `b` generate the same left ideal. -/
def IsGreenL (a b : S) : Prop := IsGreenLeftDvd a b ∧ IsGreenLeftDvd b a

/-- Green's R relation: `a` and `b` generate the same right ideal. -/
def IsGreenR (a b : S) : Prop := IsGreenRightDvd a b ∧ IsGreenRightDvd b a

/-- Green's H relation: the intersection of Green's L and Green's R relations. -/
def IsGreenH (a b : S) : Prop := IsGreenL a b ∧ IsGreenR a b

/-- Green's D relation: the composition of Green's L and Green's R relations.
Here defined explicitly as the existence of an intermediate element `z`. -/
def IsGreenD (a b : S) : Prop := ∃ z, IsGreenL a z ∧ IsGreenR z b

/-- Green's J relation: `a` and `b` generate the same two-sided ideal. -/
def IsGreenJ (a b : S) : Prop := IsGreenJRel a b ∧ IsGreenJRel b a
