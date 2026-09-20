/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Adjoint.Basic
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Representation

/-!
# The adjoint comodule of the general linear group

This file identifies the fixed-module adjoint comodule of `GLₙ` with conjugation on matrices.
It is the comodule-level adapter between the scheme-theoretic representation API and explicit
matrix subspaces.

## Main declaration

* `TauCeti.GeneralLinear.tangentMatrix_adjointComodule_endOfPoint`: the action induced by the
  adjoint comodule becomes `X ↦ g X g⁻¹` under the tangent-matrix equivalence.
-/

public section

open CategoryTheory TensorProduct WithConv
open scoped TensorProduct

namespace TauCeti.GeneralLinear

universe u

noncomputable section

variable {k : Type u} [Field k] {A : Type u} [CommRing A] [Algebra k A]
variable {n : ℕ}

private theorem counitPointsMulEquiv_pointInCounitAlgebra
    (g : HopfAlgebra.points (H := coordinateHopfAlgebra k n) (CommAlgCat.of k A)) :
    counitPointsMulEquiv n
        (Derivation.pointInCounitAlgebra (CommAlgCat.of k A) g) =
      pointsMulEquiv n g := by
  ext i j
  rw [counitPointsMulEquiv_apply, pointsMulEquiv_apply,
    pointToGeneralLinear_apply, Bialgebra.CounitAlgebra.algEquivSelf_apply,
    Derivation.pointInCounitAlgebra_apply]

/-- Under the tangent-matrix equivalence, the point action induced by the adjoint comodule of
`GLₙ` is conjugation on matrices. -/
theorem tangentMatrix_adjointComodule_endOfPoint
    (g : HopfAlgebra.points (H := coordinateHopfAlgebra k n) (CommAlgCat.of k A))
    (x : A ⊗[k]
      Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n))) :
    tangentMatrix n
        (Derivation.tangentScalarExtensionEquiv
          (R := k) (A := coordinateHopfAlgebra k n) (B := A)
          (letI := Derivation.adjointComodule
              (R := k) (H := coordinateHopfAlgebra k n)
           Comodule.endOfPoint
              (Module.Dual k
                (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n)))
              g.ofConv x)) =
      (pointsMulEquiv n g : Matrix (Fin n) (Fin n) A) *
        tangentMatrix n
          (Derivation.tangentScalarExtensionEquiv
            (R := k) (A := coordinateHopfAlgebra k n) (B := A) x) *
        ((pointsMulEquiv n g)⁻¹ : Matrix.GeneralLinearGroup (Fin n) A) := by
  have h := Derivation.tangentScalarExtensionEquiv_adjointComodule_endOfPoint
    (R := k) (H := coordinateHopfAlgebra k n) (CommAlgCat.of k A) g x
  have hm := congrArg (tangentMatrix n) h
  rw [tangentMatrix_adDerivation,
    counitPointsMulEquiv_pointInCounitAlgebra] at hm
  exact hm

end

end TauCeti.GeneralLinear
