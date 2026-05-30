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
* `IsGreenL`: Green's L relation (generating the same principal left ideal).
* `IsGreenR`: Green's R relation (generating the same principal right ideal).
* `IsGreenH`: Green's H relation (the intersection of L and R).
* `IsGreenD`: Green's D relation (the join of L and R, defined via an intermediate element).
* `IsGreenJ`: Green's J relation (generating the same principal two-sided ideal).

## References

* [T. Colombet, *The Factorization Forest Theorem*][colombet2008]

## Tags

green's relations, semigroup, divisibility, ideal
-/

variable {S : Type*} [Semigroup S]

/-- `IsGreenLeftDvd a b` means that `a` is a left multiple of `b`,
  i.e., `a = b` or `a = z * b`. -/
def IsGreenLeftDvd (a b : S) := a = b ∨ ∃ z, a = z * b

/-- `IsGreenRightDvd a b` means that `a` is a right multiple of `b`,
  i.e., `a = b` or `a = b * z`. -/
def IsGreenRightDvd (a b : S) := a = b ∨ ∃ z, a = b * z

/-- `IsGreenJRel a b` represents the basic step of being a two-sided multiple.
  `a` is related to `b` if `a = b`, `a = u * b`, `a = b * v`, or `a = u * b * v`. -/
inductive IsGreenJRel (a b : S) : Prop
  /-- `a` and `b` are equal. -/
  | refl (h : a = b)
  /-- `a` is a left multiple of `b`. -/
  | mul_left (u : S) (h : a = u * b)
  /-- `a` is a right multiple of `b`. -/
  | mul_right (v : S) (h : a = b * v)
  /-- `a` is a two-sided multiple of `b`. -/
  | mul_both (u v : S) (h : a = u * b * v)

/-- Green's L relation: `a` and `b` generate the same principal left ideal. -/
def IsGreenL (a b : S) := IsGreenLeftDvd a b ∧ IsGreenLeftDvd b a

/-- Green's R relation: `a` and `b` generate the same principal right ideal. -/
def IsGreenR (a b : S) := IsGreenRightDvd a b ∧ IsGreenRightDvd b a

/-- Green's H relation: the intersection of Green's L and Green's R relations. -/
def IsGreenH (a b : S) := IsGreenL a b ∧ IsGreenR a b

/-- Green's D relation: the join of Green's L and Green's R relations.
Here defined explicitly as the existence of an intermediate element `z`. -/
def IsGreenD (a b : S) := ∃ z, IsGreenL a z ∧ IsGreenR z b

/-- Green's J relation: `a` and `b` generate the same principal two-sided ideal. -/
def IsGreenJ (a b : S) := IsGreenJRel a b ∧ IsGreenJRel b a
