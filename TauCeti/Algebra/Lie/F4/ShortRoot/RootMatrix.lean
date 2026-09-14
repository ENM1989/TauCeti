/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.AdmissibleLattice
public import TauCeti.LinearAlgebra.Matrix.Step

/-!
# Step structure and products of the numbered simple root matrices of type F4

`TauCeti.F4ShortRoot.rootMatrix` and `TauCeti.F4ShortRoot.rootDividedSquareMatrix` are the
integral matrices of the eight numbered simple root generators of the twenty-six-dimensional
short-root representation of type `F₄` and of their divided squares. This file records the two
properties of those matrices that every later construction on them uses, independently of what
that construction is: each has at most one nonzero entry in each column, tabulated by a target
and a coefficient table, and the four products that can be formed from a generator and its
divided square are the expected multiples of one another.

The step structure is what makes entrywise identities between products of these matrices finite
computations rather than sums over the twenty-six indices, and the product relations are the
input to every expansion of a divided-power exponential in its parameter.

## Main definitions

* `TauCeti.F4ShortRoot.rootStepTarget` and `TauCeti.F4ShortRoot.rootStepCoeff`: the target and
  coefficient tables of a numbered simple root matrix, with
  `TauCeti.F4ShortRoot.rootDividedSquareStepTarget` and
  `TauCeti.F4ShortRoot.rootDividedSquareStepCoeff` those of its divided square.

## Main results

* `TauCeti.F4ShortRoot.isStep_rootMatrix` and
  `TauCeti.F4ShortRoot.isStep_rootDividedSquareMatrix`: the step structure.
* `TauCeti.F4ShortRoot.rootMatrix_mul_self`: a numbered simple root matrix squares to twice its
  divided square, with `TauCeti.F4ShortRoot.rootMatrix_mul_mul_self` its cube zero.
* `TauCeti.F4ShortRoot.rootMatrix_mul_rootDividedSquareMatrix`,
  `TauCeti.F4ShortRoot.rootDividedSquareMatrix_mul_rootMatrix` and
  `TauCeti.F4ShortRoot.rootDividedSquareMatrix_mul_self`: the remaining products vanish.

## References

The numbering follows N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VIII. The
divided-power generators are those of R. Steinberg, *Lectures on Chevalley Groups*, §3.
-/

public section

open Matrix

namespace TauCeti.F4ShortRoot

/-! ## Step structure of the numbered simple root matrices -/

/-- The target table of the numbered simple root generator matrix. -/
@[expose] def rootStepTarget : Fin 4 ⊕ Fin 4 → Fin 26 → Fin 26 :=
  Sum.elim raisingTarget loweringTarget

/-- The coefficient table of the numbered simple root generator matrix. -/
@[expose] def rootStepCoeff : Fin 4 ⊕ Fin 4 → Fin 26 → ℤ :=
  Sum.elim raisingCoeff loweringCoeff

/-- The target table of the divided square of a numbered simple root generator matrix. -/
@[expose] def rootDividedSquareStepTarget : Fin 4 ⊕ Fin 4 → Fin 26 → Fin 26 :=
  Sum.elim raisingDividedSquareTarget loweringDividedSquareTarget

/-- The coefficient table of the divided square of a numbered simple root generator matrix. -/
@[expose] def rootDividedSquareStepCoeff : Fin 4 ⊕ Fin 4 → Fin 26 → ℤ :=
  Sum.elim raisingDividedSquareCoeff loweringDividedSquareCoeff

/-- The matrix of a numbered simple root generator is a step matrix. -/
theorem isStep_rootMatrix (k : Fin 4 ⊕ Fin 4) :
    (rootMatrix k).IsStep (rootStepTarget k) (rootStepCoeff k) := by
  refine Matrix.isStep_of_apply fun a b => ?_
  cases k with
  | inl i =>
      rw [rootMatrix_inl]
      exact raisingMatrix_apply i a b
  | inr i =>
      rw [rootMatrix_inr]
      exact loweringMatrix_apply i a b

/-- The divided square of a numbered simple root generator matrix is a step matrix. -/
theorem isStep_rootDividedSquareMatrix (k : Fin 4 ⊕ Fin 4) :
    (rootDividedSquareMatrix k).IsStep (rootDividedSquareStepTarget k)
      (rootDividedSquareStepCoeff k) := by
  refine Matrix.isStep_of_apply fun a b => ?_
  cases k with
  | inl i =>
      rw [rootDividedSquareMatrix_inl]
      exact raisingDividedSquareMatrix_apply i a b
  | inr i =>
      rw [rootDividedSquareMatrix_inr]
      exact loweringDividedSquareMatrix_apply i a b

/-! ## Products of the numbered simple root matrices -/

/-- The square of a numbered simple root matrix is twice its divided square. -/
theorem rootMatrix_mul_self (k : Fin 4 ⊕ Fin 4) :
    rootMatrix k * rootMatrix k = (2 : ℤ) • rootDividedSquareMatrix k := by
  cases k with
  | inl i => rw [rootMatrix_inl, rootDividedSquareMatrix_inl, raisingMatrix_mul_self]
  | inr i => rw [rootMatrix_inr, rootDividedSquareMatrix_inr, loweringMatrix_mul_self]

/-- A numbered simple root matrix annihilates its divided square on the left. -/
@[simp]
theorem rootMatrix_mul_rootDividedSquareMatrix (k : Fin 4 ⊕ Fin 4) :
    rootMatrix k * rootDividedSquareMatrix k = 0 := by
  cases k with
  | inl i =>
      rw [rootMatrix_inl, rootDividedSquareMatrix_inl,
        raisingMatrix_mul_raisingDividedSquareMatrix]
  | inr i =>
      rw [rootMatrix_inr, rootDividedSquareMatrix_inr,
        loweringMatrix_mul_loweringDividedSquareMatrix]

/-- A numbered simple root matrix annihilates its divided square on the right. -/
@[simp]
theorem rootDividedSquareMatrix_mul_rootMatrix (k : Fin 4 ⊕ Fin 4) :
    rootDividedSquareMatrix k * rootMatrix k = 0 := by
  cases k with
  | inl i =>
      rw [rootMatrix_inl, rootDividedSquareMatrix_inl,
        raisingDividedSquareMatrix_mul_raisingMatrix]
  | inr i =>
      rw [rootMatrix_inr, rootDividedSquareMatrix_inr,
        loweringDividedSquareMatrix_mul_loweringMatrix]

/-- A numbered simple root matrix cubes to zero. -/
theorem rootMatrix_mul_mul_self (k : Fin 4 ⊕ Fin 4) :
    rootMatrix k * rootMatrix k * rootMatrix k = 0 := by
  rw [rootMatrix_mul_self, smul_mul_assoc, rootDividedSquareMatrix_mul_rootMatrix, smul_zero]

/-- The divided square of a numbered simple root matrix squares to zero. -/
@[simp]
theorem rootDividedSquareMatrix_mul_self (k : Fin 4 ⊕ Fin 4) :
    rootDividedSquareMatrix k * rootDividedSquareMatrix k = 0 := by
  have h2 : ((2 : ℤ) • rootDividedSquareMatrix k) * ((2 : ℤ) • rootDividedSquareMatrix k) =
      (4 : ℤ) • (rootDividedSquareMatrix k * rootDividedSquareMatrix k) := by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]
    norm_num
  have h : (4 : ℤ) • (rootDividedSquareMatrix k * rootDividedSquareMatrix k) = 0 := by
    rw [← h2, ← rootMatrix_mul_self, ← mul_assoc, rootMatrix_mul_mul_self, zero_mul]
  exact (smul_eq_zero.mp h).resolve_left (by norm_num)
end TauCeti.F4ShortRoot
