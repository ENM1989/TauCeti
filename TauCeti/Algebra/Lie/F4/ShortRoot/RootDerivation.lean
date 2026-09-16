/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Derivation
public import TauCeti.Algebra.Lie.F4.ShortRoot.QuotientCoordinates

/-!
# The numbered simple root generators of type F4 differentiate the multiplication

The Lie algebra of type `F₄` acts on its twenty-six-dimensional module by derivations of the
invariant symmetric multiplication. This file reduces that statement for a numbered simple root
generator to a finite family of relations between the sparse structure tables.

## Main results

* `TauCeti.F4ShortRoot.isDerivation_rootMatrix_of_entries`: the derivation property of a numbered
  simple root generator, reduced to its entrywise form.
-/

public section

open Matrix

namespace TauCeti.F4ShortRoot

/-- **The derivation equations of a numbered simple root generator, entry by entry.** -/
theorem isDerivation_rootMatrix_of_entries (k : Fin 4 ⊕ Fin 4)
    (h : ∀ c : Fin 26, ∀ p : Fin 26 × Fin 26,
      (if p.1 = rootStepTarget k (multTargetOne c p.2) then
            rootStepCoeff k (multTargetOne c p.2) else 0) * multCoeffOne c p.2 +
          (if p.1 = rootStepTarget k (multTargetTwo c p.2) then
            rootStepCoeff k (multTargetTwo c p.2) else 0) * multCoeffTwo c p.2 -
          ((if p.1 = multTargetOne c (rootStepTarget k p.2) then
                multCoeffOne c (rootStepTarget k p.2) else 0) +
              (if p.1 = multTargetTwo c (rootStepTarget k p.2) then
                multCoeffTwo c (rootStepTarget k p.2) else 0)) * rootStepCoeff k p.2 =
        rootStepCoeff k c *
          ((if p.1 = multTargetOne (rootStepTarget k c) p.2 then
              multCoeffOne (rootStepTarget k c) p.2 else 0) +
            (if p.1 = multTargetTwo (rootStepTarget k c) p.2 then
              multCoeffTwo (rootStepTarget k c) p.2 else 0))) :
    IsDerivation (rootMatrix k) := by
  rw [isDerivation_int_iff]
  intro c
  rw [Matrix.IsStep.sum_smul (isStep_rootMatrix k)]
  ext p q
  rw [Matrix.sub_apply,
    Matrix.IsDoubleStep.mul_apply (isDoubleStep_multiplicationOperator c) (rootMatrix k) p q,
    Matrix.IsStep.mul_apply (isStep_rootMatrix k) (multiplicationOperator c) p q,
    Matrix.smul_apply, smul_eq_mul, (isStep_rootMatrix k).apply, (isStep_rootMatrix k).apply,
    multiplicationOperator_apply, multiplicationOperator_apply]
  exact h c (p, q)

end TauCeti.F4ShortRoot
