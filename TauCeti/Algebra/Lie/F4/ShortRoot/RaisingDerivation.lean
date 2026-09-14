/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Derivation
public import TauCeti.Algebra.Lie.F4.ShortRoot.StepTranspose

/-!
# The numbered simple raising generators of type F4 differentiate the multiplication

The Lie algebra of type `F₄` acts on its twenty-six-dimensional module by derivations of the
invariant symmetric multiplication; equivalently, that multiplication is a morphism of modules
from the symmetric square. This file records that for the four numbered simple raising generators,
over the integers.

A generator carries each weight vector of the basis to a multiple of a weight vector, and each
product of two weight vectors is a combination of at most two of them, so the derivation equation
of a generator is a finite family of relations between the structure constants of the
multiplication and the coefficients of the generator, one for each pair of a column of the
multiplication and a matrix entry.

## Main results

* `TauCeti.F4ShortRoot.isDerivation_raisingMatrix`: **each numbered simple raising generator is a
  derivation of the invariant multiplication.**

## References

* N. Jacobson, *Exceptional Lie Algebras*, Lecture Notes in Pure and Applied Mathematics **1**,
  Marcel Dekker (1971), §I.4.
-/

public section

open Matrix

namespace TauCeti.F4ShortRoot

/-- The zeroth numbered simple raising generator differentiates the invariant multiplication. -/
private theorem isDerivation_raisingMatrix_zero : IsDerivation (rootMatrix (Sum.inl 0)) := by
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

/-- The first numbered simple raising generator differentiates the invariant multiplication. -/
private theorem isDerivation_raisingMatrix_one : IsDerivation (rootMatrix (Sum.inl 1)) := by
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

/-- The second numbered simple raising generator differentiates the invariant multiplication. -/
private theorem isDerivation_raisingMatrix_two : IsDerivation (rootMatrix (Sum.inl 2)) := by
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

/-- The third numbered simple raising generator differentiates the invariant multiplication. -/
private theorem isDerivation_raisingMatrix_three : IsDerivation (rootMatrix (Sum.inl 3)) := by
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

/-- **Every numbered simple raising generator of the twenty-six-dimensional module of type `F₄`
differentiates the invariant symmetric multiplication.** -/
theorem isDerivation_raisingMatrix (i : Fin 4) : IsDerivation (raisingMatrix i) := by
  fin_cases i
  · exact isDerivation_raisingMatrix_zero
  · exact isDerivation_raisingMatrix_one
  · exact isDerivation_raisingMatrix_two
  · exact isDerivation_raisingMatrix_three

end TauCeti.F4ShortRoot
