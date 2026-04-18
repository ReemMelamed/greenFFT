# Simon's Factorization Forest theorem and Green's relations (Lean 4)

Formalization in Lean 4 of algebraic components behind Simon's Factorization Forest Theorem,
with a focus on Green's relations.

## Reference article

- Thomas Colcombet, *The factorization Forest Theorem*: 
  <https://www.irif.fr/~colcombe/Publications/handbook-fft-colcombet_non-final.pdf>

## What this repository formalizes

```text
- Green's relations: L, R, H, D, J
- Equivalence classes and quotient constructions for Green's relations
- Finite-semigroup structure results (regular D-classes, idempotents, D = J)
- Special cases of Simon's theorem: group case, H-class case, and regular D-class case
```

## Overview

### `Semigroup/GreensRelations/`

* `Defs.lean`
  - Contains the foundational definitions for Green's relations (L, R, H, D, and J) and left/right divisibility over semigroups. 
  - Establishes the basic logical predicates used throughout the entire library.

* `Basic.lean`
  - Proves the foundational equivalences and sets up the relations as formal setoids.
  - Establishes the vital duality of left and right divisibility by utilizing the opposite semigroup (MulOpposite).

* `Classes.lean`
  - Defines the equivalence classes and quotient spaces for the relations.
  - Proves that these quotient spaces form partial orders and formally defines the notions of regular elements and regular D-classes.
 
* `MulSeq.lean`
  - Provides tools for analyzing finite semigroups using iterated multiplication sequences.
  - Structural helper lemmas, such as applications of the pigeonhole principle.
 
* `Theorems.lean`
  - The major structural theorems of Green's relations.
  - Key results like the proof that D and J relations are strictly equal in finite semigroups,
Green's lemma (constructing explicit bijections between H-classes), and the proof that an H-class is either a group or contains no idempotents.

### `Semigroup/`

* `Simon.lean`
  - Contains the core components of Simon's Factorization Forest theorem.
  - Defines the necessary structures like multiplicative labeling, normalized split, and Ramsey split.
  - Holds the formal proofs for the group case, the subgroup H-class case, and the regular D-class case.
