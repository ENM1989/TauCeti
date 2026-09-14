/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Derivation
public import TauCeti.Algebra.Lie.F4.ShortRoot.StepTranspose

/-!
# The numbered simple lowering generators of type F4 differentiate the multiplication

The Lie algebra of type `F₄` acts on its twenty-six-dimensional module by derivations of the
invariant symmetric multiplication; equivalently, that multiplication is a morphism of modules
from the symmetric square. This file records that for the four numbered simple lowering generators,
over the integers.

A generator carries each weight vector of the basis to a multiple of a weight vector, and each
product of two weight vectors is a combination of at most two of them, so the derivation equation
of a generator is a finite family of relations between the structure constants of the
multiplication and the coefficients of the generator, one for each pair of a column of the
multiplication and a matrix entry.

## Main results

* `TauCeti.F4ShortRoot.isDerivation_loweringMatrix`: **each numbered simple lowering generator is a
  derivation of the invariant multiplication.**

## References

* N. Jacobson, *Exceptional Lie Algebras*, Lecture Notes in Pure and Applied Mathematics **1**,
  Marcel Dekker (1971), §I.4.
-/

public section

open Matrix

namespace TauCeti.F4ShortRoot

/-- The zeroth numbered simple lowering generator differentiates the invariant multiplication. -/
private theorem isDerivation_loweringMatrix_zero : IsDerivation (rootMatrix (Sum.inr 0)) := by
  rw [isDerivation_int_iff]
  intro c
  rw [Matrix.IsStep.sum_smul (isStep_rootMatrix _)]
  ext p q
  rw [Matrix.sub_apply,
    Matrix.IsDoubleStep.transpose_mul_apply (isDoubleStep_transpose_rootMatrix _),
    Matrix.IsStep.mul_apply (isStep_rootMatrix _), Matrix.smul_apply, smul_eq_mul]
  simp only [multiplicationOperator_apply]
  revert c p q
  decide +kernel

/-- The first numbered simple lowering generator differentiates the invariant multiplication. -/
private theorem isDerivation_loweringMatrix_one : IsDerivation (rootMatrix (Sum.inr 1)) := by
  rw [isDerivation_int_iff]
  intro c
  rw [Matrix.IsStep.sum_smul (isStep_rootMatrix _)]
  ext p q
  rw [Matrix.sub_apply,
    Matrix.IsDoubleStep.transpose_mul_apply (isDoubleStep_transpose_rootMatrix _),
    Matrix.IsStep.mul_apply (isStep_rootMatrix _), Matrix.smul_apply, smul_eq_mul]
  simp only [multiplicationOperator_apply]
  revert c p q
  decide +kernel

/-- The second numbered simple lowering generator differentiates the invariant multiplication. -/
private theorem isDerivation_loweringMatrix_two : IsDerivation (rootMatrix (Sum.inr 2)) := by
  rw [isDerivation_int_iff]
  intro c
  rw [Matrix.IsStep.sum_smul (isStep_rootMatrix _)]
  ext p q
  rw [Matrix.sub_apply,
    Matrix.IsDoubleStep.transpose_mul_apply (isDoubleStep_transpose_rootMatrix _),
    Matrix.IsStep.mul_apply (isStep_rootMatrix _), Matrix.smul_apply, smul_eq_mul]
  simp only [multiplicationOperator_apply]
  revert c p q
  decide +kernel

/-- The third numbered simple lowering generator differentiates the invariant multiplication. -/
private theorem isDerivation_loweringMatrix_three : IsDerivation (rootMatrix (Sum.inr 3)) := by
  rw [isDerivation_int_iff]
  intro c
  rw [Matrix.IsStep.sum_smul (isStep_rootMatrix _)]
  ext p q
  rw [Matrix.sub_apply,
    Matrix.IsDoubleStep.transpose_mul_apply (isDoubleStep_transpose_rootMatrix _),
    Matrix.IsStep.mul_apply (isStep_rootMatrix _), Matrix.smul_apply, smul_eq_mul]
  simp only [multiplicationOperator_apply]
  revert c p q
  decide +kernel

/-- **Every numbered simple lowering generator of the twenty-six-dimensional module of type `F₄`
differentiates the invariant symmetric multiplication.** -/
theorem isDerivation_loweringMatrix (i : Fin 4) : IsDerivation (loweringMatrix i) := by
  fin_cases i
  · exact isDerivation_loweringMatrix_zero
  · exact isDerivation_loweringMatrix_one
  · exact isDerivation_loweringMatrix_two
  · exact isDerivation_loweringMatrix_three

end TauCeti.F4ShortRoot
