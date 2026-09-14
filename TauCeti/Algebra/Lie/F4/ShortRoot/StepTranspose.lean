/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.QuotientCoordinates

/-!
# Rows of the numbered simple root matrices of type F4

Each numbered simple root generator of the twenty-six-dimensional module of type `F₄` carries a
weight vector of the basis to a multiple of a weight vector, so its matrix has at most one nonzero
entry in each column. In the other direction a generator can send two basis vectors to multiples
of the same one, because the zero weight space is two-dimensional, so its transpose has at most
two nonzero entries in each column. This file tabulates that transposed structure, for the eight
numbered simple root matrices and for their divided squares, whose transposes again have at most
one nonzero entry in each column.

These tables are what makes an entry of a product with a generator on the left a sum of two
products of table lookups, as `Matrix.IsDoubleStep.transpose_mul_apply` records; the tables for
the columns, which govern a product with a generator on the right, are those of
`TauCeti.Algebra.Lie.F4.ShortRoot.QuotientCoordinates`.

## Main definitions

* `TauCeti.F4ShortRoot.rootTransposeTargetOne` and its three companions: the transposed step
  tables of a numbered simple root matrix.
* `TauCeti.F4ShortRoot.rootDividedSquareTransposeTarget` and
  `TauCeti.F4ShortRoot.rootDividedSquareTransposeCoeff`: the transposed step tables of a divided
  square.

## Main results

* `TauCeti.F4ShortRoot.isDoubleStep_transpose_rootMatrix`: the transpose of a numbered simple root
  matrix has at most two nonzero entries in each column.
* `TauCeti.F4ShortRoot.isStep_transpose_rootDividedSquareMatrix`: the transpose of a divided square
  has at most one.
-/

public section

open Matrix

namespace TauCeti.F4ShortRoot

/-- The first target of each column of the transpose of a numbered simple root matrix. -/
@[expose] def rootTransposeTargetOne : Fin 4 ⊕ Fin 4 → Fin 26 → Fin 26 :=
  Sum.elim
    ![![0, 0, 0, 4, 0, 6, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 18, 0, 0, 20, 0, 22, 0, 0, 0, 0],
      ![0, 0, 3, 0, 0, 0, 8, 0, 0, 11, 0, 0, 0, 0, 16, 0, 0, 19, 0, 0, 0, 0, 23, 0, 0, 0],
      ![0, 2, 0, 5, 6, 0, 0, 0, 10, 0, 0, 12, 14, 0, 0, 17, 0, 0, 0, 21, 22, 0, 0, 24, 0, 0],
      ![1, 0, 0, 0, 0, 7, 9, 0, 11, 0, 12, 0, 0, 15, 17, 0, 19, 0, 20, 0, 0, 0, 0, 0, 25, 0]]
    ![![0, 0, 0, 0, 3, 0, 5, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 16, 0, 19, 0, 21, 0, 0, 0],
      ![0, 0, 0, 2, 0, 0, 0, 0, 6, 0, 0, 9, 0, 0, 0, 0, 14, 0, 0, 17, 0, 0, 0, 22, 0, 0],
      ![0, 0, 1, 0, 0, 3, 4, 0, 0, 0, 8, 0, 11, 0, 12, 0, 0, 15, 0, 0, 0, 19, 20, 0, 23, 0],
      ![0, 0, 0, 0, 0, 0, 0, 5, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 16, 18, 0, 0, 0, 0, 24]]

/-- The coefficient of the first target of each column of the transpose of a numbered simple root
matrix. -/
@[expose] def rootTransposeCoeffOne : Fin 4 ⊕ Fin 4 → Fin 26 → ℤ :=
  Sum.elim
    ![![0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0],
      ![0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0],
      ![0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 2, 1, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0],
      ![1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0]]
    ![![0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0],
      ![0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0],
      ![0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 2, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0],
      ![0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1]]

/-- The second target of each column of the transpose of a numbered simple root matrix, taken to
be the zeroth index when the column has at most one nonzero entry. -/
@[expose] def rootTransposeTargetTwo : Fin 4 ⊕ Fin 4 → Fin 26 → Fin 26 :=
  Sum.elim
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- The coefficient of the second target of each column of the transpose of a numbered simple root
matrix. -/
@[expose] def rootTransposeCoeffTwo : Fin 4 ⊕ Fin 4 → Fin 26 → ℤ :=
  Sum.elim
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- The target of each column of the transpose of the divided square of a numbered simple root
matrix. -/
@[expose] def rootDividedSquareTransposeTarget : Fin 4 ⊕ Fin 4 → Fin 26 → Fin 26 :=
  Sum.elim
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- The coefficient of each column of the transpose of the divided square of a numbered simple
root matrix. -/
@[expose] def rootDividedSquareTransposeCoeff : Fin 4 ⊕ Fin 4 → Fin 26 → ℤ :=
  Sum.elim
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- **The transpose of a numbered simple root matrix has at most two nonzero entries in each
column**, at the tabulated targets and with the tabulated coefficients. -/
theorem isDoubleStep_transpose_rootMatrix (k : Fin 4 ⊕ Fin 4) :
    (rootMatrix k)ᵀ.IsDoubleStep (rootTransposeTargetOne k) (rootTransposeCoeffOne k)
      (rootTransposeTargetTwo k) (rootTransposeCoeffTwo k) := by
  intro a b
  rw [Matrix.transpose_apply, isStep_rootMatrix k]
  revert k a b
  decide +kernel

/-- **The transpose of the divided square of a numbered simple root matrix has at most one nonzero
entry in each column**, at the tabulated target and with the tabulated coefficient. -/
theorem isStep_transpose_rootDividedSquareMatrix (k : Fin 4 ⊕ Fin 4) :
    (rootDividedSquareMatrix k)ᵀ.IsStep (rootDividedSquareTransposeTarget k)
      (rootDividedSquareTransposeCoeff k) := by
  intro a b
  rw [Matrix.transpose_apply, isStep_rootDividedSquareMatrix k]
  revert k a b
  decide +kernel

end TauCeti.F4ShortRoot
