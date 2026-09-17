/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Coordinate
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.FromMatrix

/-!
# Coordinate morphisms out of `GLₙ` determined by a grouplike matrix

A square matrix `Y` over a commutative Hopf algebra `S` is **grouplike** when

```text
Y.map Δ = (Y ⊗ 1) (1 ⊗ Y),   Y.map ε = 1,
```

that is, when each entry comultiplies as `Δ Yᵢⱼ = ∑ₖ Yᵢₖ ⊗ Yₖⱼ` and counits to the corresponding
entry of the identity matrix. These are exactly the conditions making the columns of `Y` a
coaction of `S` on the free module `Rⁿ`, so a grouplike matrix determines a morphism of
commutative Hopf algebras

```text
O(GLₙ) →ₐc[R] S
```

carrying the generic matrix to `Y`. Contravariantly, a grouplike matrix over the coordinate Hopf
algebra of an affine group scheme `G` is the same thing as a homomorphism `G → GLₙ`, hence the
same thing as an `n`-dimensional representation of `G`; the conditions say that the matrix is
multiplicative and unital on points, functorially in the value algebra.

The determinant of a grouplike matrix is automatically invertible — it is a grouplike element of
`S` — so no separate hypothesis is needed to land in `GLₙ` rather than in the matrix monoid.

The comodule uses only the comultiplication and the counit of `S`, so it is built over a
bialgebra. The coordinate morphism needs more: the coordinate algebra of `GLₙ` inverts the
determinant, and the entries of the inverse matrix are received through the antipode, so that
half of the file asks for a Hopf algebra.

The construction is the comodule of the matrix followed by
`TauCeti.Comodule.coordinateBialgHom`, the coordinate morphism of a comodule with a basis. The
generic matrix of `GLₙ` is the case `S = O(GLₙ)` and `Y = X`, where the resulting morphism is the
identity.

## Main declarations

* `TauCeti.GeneralLinear.matrixCoact` and `TauCeti.GeneralLinear.matrixComodule`: the candidate
  coaction on column vectors given by the columns of a matrix, and the comodule it defines when the
  matrix is grouplike, with `TauCeti.GeneralLinear.matrixComodule_coact` unfolding the latter's
  coaction and `TauCeti.GeneralLinear.coefficientMatrix_matrixComodule` computing its coefficient
  matrix.
* `TauCeti.GeneralLinear.coordinateBialgHomOfGroupLike`: the coordinate morphism of a grouplike
  matrix, with `TauCeti.GeneralLinear.coordinateBialgHomOfGroupLike_X` and
  `TauCeti.GeneralLinear.map_genericMatrix_coordinateBialgHomOfGroupLike` identifying its value on
  the generic matrix.
* `TauCeti.GeneralLinear.map_comul_iff` and `TauCeti.GeneralLinear.map_counit_iff`: the matrix
  conditions characterized entrywise.
* `TauCeti.GeneralLinear.map_comul_map_genericMatrix` and
  `TauCeti.GeneralLinear.map_counit_map_genericMatrix`: the image of the generic matrix under a
  morphism of commutative bialgebras is grouplike.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes* (1979), §3.2, where representations of
  an affine group scheme are matched with comodules through their matrix coefficients.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.8.

The standard comodule `TauCeti.GeneralLinear.standardComodule` is obtained by specializing this
construction to the generic matrix.
-/

public section

open Module WithConv
open scoped TensorProduct

namespace TauCeti.GeneralLinear

universe u v

variable (R : Type u) (n : ℕ)


/-! ### The generic matrix transported along a coordinate morphism -/

section Transport

variable [CommRing R] {S : Type v} [Semiring S] [Bialgebra R S] {R n}
variable (φ : coordinateHopfAlgebra R n →ₐc[R] S)

/-- **The comultiplication condition for the generic matrix transported along a morphism of
commutative bialgebras.** The image of the generic matrix under any such morphism is
grouplike, since the generic matrix is and the morphism respects comultiplication. -/
theorem map_comul_map_genericMatrix :
    ((genericMatrix R n).map φ).map (Bialgebra.comulAlgHom R S) =
      ((genericMatrix R n).map φ).map (Algebra.TensorProduct.includeLeft (R := R) (S := R)) *
        ((genericMatrix R n).map φ).map (Algebra.TensorProduct.includeRight (R := R)) := by
  rw [map_comul_iff]
  intro i j
  have hgeneric :=
    (map_comul_iff R n (genericMatrix R n)).mp (map_comul_genericMatrix R n) i j
  calc
    Coalgebra.comul (R := R) (((genericMatrix R n).map φ) i j) =
        Algebra.TensorProduct.map φ.toAlgHom φ.toAlgHom
          (Coalgebra.comul (R := R) ((genericMatrix R n) i j)) := by
      rw [Matrix.map_apply]
      exact (CoalgHomClass.map_comp_comul_apply φ _).symm
    _ = Algebra.TensorProduct.map φ.toAlgHom φ.toAlgHom
          (∑ k, (genericMatrix R n) i k ⊗ₜ[R] (genericMatrix R n) k j) := by
      rw [hgeneric]
    _ = ∑ k, ((genericMatrix R n).map φ) i k ⊗ₜ[R]
          ((genericMatrix R n).map φ) k j := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Algebra.TensorProduct.map_tmul, Matrix.map_apply, BialgHom.coe_toAlgHom]

/-- **The counit condition for the generic matrix transported along a morphism of commutative
bialgebras.** -/
theorem map_counit_map_genericMatrix :
    ((genericMatrix R n).map φ).map (Bialgebra.counitAlgHom R S) = 1 := by
  have hcounit : (Bialgebra.counitAlgHom R S : S → R) ∘ (φ : _ → S) =
      (Bialgebra.counitAlgHom R (coordinateHopfAlgebra R n) : _ → R) :=
    funext fun x => CoalgHomClass.counit_comp_apply φ x
  rw [Matrix.map_map, hcounit, map_counit_genericMatrix]

end Transport

/-! ### The coordinate morphism of a grouplike matrix

The coordinate algebra of `GLₙ` inverts the determinant, so a morphism out of it needs the
antipode of `S` to receive the entries of the inverse matrix; this part asks for a Hopf
algebra. -/

section CoordinateMorphism

variable [CommRing R]
variable {S : Type v} [CommRing S] [HopfAlgebra R S]
variable (Y : Matrix (Fin n) (Fin n) S)
variable (hcomul : Y.map (Bialgebra.comulAlgHom R S) =
    Y.map (Algebra.TensorProduct.includeLeft (R := R) (S := R)) *
      Y.map (Algebra.TensorProduct.includeRight (R := R)))
variable (hcounit : Y.map (Bialgebra.counitAlgHom R S) = 1)

include hcomul hcounit in
/-- **The coordinate morphism of a grouplike matrix**: the morphism of commutative Hopf algebras
out of the coordinate algebra of `GL n` sending the generic matrix to `Y`. -/
noncomputable def coordinateBialgHomOfGroupLike :
    coordinateHopfAlgebra R n →ₐc[R] S := by
  letI : Comodule R S (Fin n → R) := matrixComodule R n Y hcomul hcounit
  exact Comodule.coordinateBialgHom (Pi.basisFun R (Fin n))

include hcomul hcounit in
/-- The coordinate morphism of a grouplike matrix sends a generic matrix entry to the
corresponding entry of the matrix. -/
@[simp]
theorem coordinateBialgHomOfGroupLike_X (i j : Fin n) :
    coordinateBialgHomOfGroupLike R n Y hcomul hcounit
        (coordinateHopfAlgebraAlgEquiv R n
          (coordinateRingMap R n (MvPolynomial.X (i, j)))) = Y i j := by
  let : Comodule R S (Fin n → R) := matrixComodule R n Y hcomul hcounit
  refine Eq.trans (Comodule.coordinateBialgHom_X (H := S) (Pi.basisFun R (Fin n)) i j) ?_
  exact congrFun (congrFun (coefficientMatrix_matrixComodule R n Y hcomul hcounit) i) j

include hcomul hcounit in
/-- The coordinate morphism of a grouplike matrix carries the generic matrix to that matrix. -/
@[simp]
theorem map_genericMatrix_coordinateBialgHomOfGroupLike :
    (genericMatrix R n).map (coordinateBialgHomOfGroupLike R n Y hcomul hcounit) = Y := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.map_apply, genericMatrix_apply, coordinateBialgHomOfGroupLike_X]

/-- Reconstructing a bialgebra morphism from its image of the generic matrix returns the original
morphism. -/
@[simp]
theorem coordinateBialgHomOfGroupLike_map_genericMatrix
    (φ : coordinateHopfAlgebra R n →ₐc[R] S) :
    coordinateBialgHomOfGroupLike R n ((genericMatrix R n).map φ)
        (map_comul_map_genericMatrix φ) (map_counit_map_genericMatrix φ) = φ := by
  apply coordinateHopfAlgebra_bialgHom_ext
  intro i j
  rw [coordinateBialgHomOfGroupLike_X, Matrix.map_apply, genericMatrix_apply]

end CoordinateMorphism

end TauCeti.GeneralLinear
