/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Matrix.IntegralCast
public import TauCeti.Algebra.Lie.Presentation.MinusculeWeightTable
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.CoordinateLattice
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Serre
import TauCeti.LinearAlgebra.Matrix.MulVec

/-!
# The admissible lattice of a minuscule weight table

The integral Chevalley generators a minuscule weight table names extend to the rational Serre
algebra, and the coordinate `ℤ`-lattice of the rational module they act on is preserved by the
Serre Kostant form. This file proves that once, for an arbitrary table, so that a carrier built
on one reads its rational representation and its admissible lattice off the table.

The raising and lowering matrices have entries in `ℤ` and are square-zero, so they preserve the
coordinate lattice and act nilpotently; the Cartan matrices are diagonal with the table's weights
on the diagonal, so every standard coordinate vector is a Cartan weight vector with an integral
weight. Those are the two inputs of the generic Kostant stability theorem.

Together with the statement that the weights span the character lattice, which is a property of
the individual table rather than of every table, these are the lattice inputs a Chevalley carrier
needs.

## Main declarations

* `TauCeti.MinusculeWeightTable.raisingMatrixQ`, `loweringMatrixQ` and `cartanGeneratorMatrixQ`:
  the rational Chevalley generators.
* `TauCeti.MinusculeWeightTable.rationalSerreRepresentation`: the rational representation of the
  Serre presentation.
* `TauCeti.MinusculeWeightTable.rep`: its extension to the universal enveloping algebra.

## Main results

* `TauCeti.MinusculeWeightTable.isSerreSystemQ`: the rational generators satisfy the Serre
  relations.
* `TauCeti.MinusculeWeightTable.rep_serreKostantForm_mem_lattice`: the Serre Kostant form
  preserves `TauCeti.coordinateLattice`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§26--27.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1--2.
-/

public section

open scoped Matrix

namespace TauCeti.MinusculeWeightTable

attribute [local instance 100] LieRing.ofAssociativeRing

variable {B ι : Type*} [Fintype ι] [DecidableEq ι] (T : MinusculeWeightTable B ι)

/-! ## The rational Chevalley generators -/

/-- The rational raising matrix of the `i`-th simple root. -/
noncomputable def raisingMatrixQ (i : B) : Matrix ι ι ℚ :=
  matrixIntCastLieHom ℚ (T.raisingMatrix i)

/-- The rational lowering matrix of the `i`-th simple root. -/
noncomputable def loweringMatrixQ (i : B) : Matrix ι ι ℚ :=
  matrixIntCastLieHom ℚ (T.loweringMatrix i)

/-- The rational Cartan generator matrix of the `i`-th simple coroot. -/
noncomputable def cartanGeneratorMatrixQ (i : B) : Matrix ι ι ℚ :=
  matrixIntCastLieHom ℚ (T.cartanGeneratorMatrix i)

/-- The entries of a rational raising matrix are the zero-one coefficients of the integral one. -/
@[simp]
theorem raisingMatrixQ_apply (i : B) (a b : ι) :
    T.raisingMatrixQ i a b =
      if T.weight b i = -1 ∧ a = T.reflection i b then 1 else 0 := by
  rw [raisingMatrixQ, matrixIntCastLieHom_apply, T.raisingMatrix_apply]
  split_ifs <;> norm_num

/-- The entries of a rational lowering matrix are the zero-one coefficients of the integral
one. -/
@[simp]
theorem loweringMatrixQ_apply (i : B) (a b : ι) :
    T.loweringMatrixQ i a b =
      if T.weight b i = 1 ∧ a = T.reflection i b then 1 else 0 := by
  rw [loweringMatrixQ, matrixIntCastLieHom_apply, T.loweringMatrix_apply]
  split_ifs <;> norm_num

/-- The rational Cartan generator is diagonal with the table's weights on its diagonal. -/
@[simp]
theorem cartanGeneratorMatrixQ_apply (i : B) (a b : ι) :
    T.cartanGeneratorMatrixQ i a b = if a = b then (T.weight b i : ℚ) else 0 := by
  rw [cartanGeneratorMatrixQ, matrixIntCastLieHom_apply, T.cartanGeneratorMatrix_apply]
  split_ifs <;> norm_num

/-- Every rational raising matrix is square-zero. -/
@[simp]
theorem raisingMatrixQ_pow_two (i : B) : T.raisingMatrixQ i ^ 2 = 0 := by
  rw [raisingMatrixQ, pow_two, ← matrixIntCastLieHom_mul, ← pow_two, T.raisingMatrix_pow_two,
    map_zero]

/-- Every rational lowering matrix is square-zero. -/
@[simp]
theorem loweringMatrixQ_pow_two (i : B) : T.loweringMatrixQ i ^ 2 = 0 := by
  rw [loweringMatrixQ, pow_two, ← matrixIntCastLieHom_mul, ← pow_two, T.loweringMatrix_pow_two,
    map_zero]

/-! ## The rational Serre presentation -/

variable [DecidableEq B]

omit [DecidableEq B] in
/-- **The rational matrices of a minuscule weight table satisfy the Serre relations of its Cartan
matrix.** -/
theorem isSerreSystemQ :
    TauCeti.IsSerreSystem ℚ T.cartanMatrix T.cartanGeneratorMatrixQ T.raisingMatrixQ
      T.loweringMatrixQ := by
  have h := T.isSerreSystem.map (matrixIntCastLieHom ℚ)
  have hH : matrixIntCastLieHom ℚ ∘ T.cartanGeneratorMatrix = T.cartanGeneratorMatrixQ := rfl
  have hE : matrixIntCastLieHom ℚ ∘ T.raisingMatrix = T.raisingMatrixQ := rfl
  have hF : matrixIntCastLieHom ℚ ∘ T.loweringMatrix = T.loweringMatrixQ := rfl
  rw [hH, hE, hF] at h
  exact h.restrictScalars

/-- The rational representation of the Serre presentation named by a minuscule weight table. -/
noncomputable def rationalSerreRepresentation :
    Matrix.ToLieAlgebra ℚ T.cartanMatrix →ₗ⁅ℚ⁆ Matrix ι ι ℚ :=
  TauCeti.serreLift T.isSerreSystemQ

/-- The rational representation sends a Cartan generator to its diagonal weight matrix. -/
@[simp]
theorem rationalSerreRepresentation_serreH (i : B) :
    T.rationalSerreRepresentation (TauCeti.serreH ℚ T.cartanMatrix i) =
      T.cartanGeneratorMatrixQ i :=
  TauCeti.serreLift_serreH T.isSerreSystemQ i

/-- The rational representation sends a positive generator to its raising matrix. -/
@[simp]
theorem rationalSerreRepresentation_serreE (i : B) :
    T.rationalSerreRepresentation (TauCeti.serreE ℚ T.cartanMatrix i) = T.raisingMatrixQ i :=
  TauCeti.serreLift_serreE T.isSerreSystemQ i

/-- The rational representation sends a negative generator to its lowering matrix. -/
@[simp]
theorem rationalSerreRepresentation_serreF (i : B) :
    T.rationalSerreRepresentation (TauCeti.serreF ℚ T.cartanMatrix i) = T.loweringMatrixQ i :=
  TauCeti.serreLift_serreF T.isSerreSystemQ i

/-! ## The enveloping-algebra representation -/

/-- The rational representation extended to the universal enveloping algebra. -/
noncomputable def rep :
    _root_.UniversalEnvelopingAlgebra ℚ (Matrix.ToLieAlgebra ℚ T.cartanMatrix) →ₐ[ℚ]
      Module.End ℚ (ι → ℚ) :=
  _root_.UniversalEnvelopingAlgebra.lift ℚ
    ((Matrix.toLinAlgEquiv (Pi.basisFun ℚ ι)).toAlgHom.toLieHom.comp
      T.rationalSerreRepresentation)

/-- The enveloping-algebra representation acts on an included Lie element by matrix-vector
multiplication. -/
theorem rep_ι_apply (x : Matrix.ToLieAlgebra ℚ T.cartanMatrix) (v : ι → ℚ) :
    T.rep (_root_.UniversalEnvelopingAlgebra.ι ℚ x) v = T.rationalSerreRepresentation x *ᵥ v := by
  rw [rep, _root_.UniversalEnvelopingAlgebra.lift_ι_apply, LieHom.comp_apply,
    AlgHom.toLieHom_apply, AlgEquiv.toAlgHom_apply, Matrix.toLinAlgEquiv_apply]
  exact (Pi.basisFun ℚ ι).sum_repr (T.rationalSerreRepresentation x *ᵥ v)

/-- Every represented positive or negative Serre root generator is square-zero. -/
theorem rep_serreRootGenerator_pow_two (k : B ⊕ B) :
    T.rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
      (TauCeti.serreRootGenerator T.cartanMatrix k)) ^ 2 = 0 := by
  apply LinearMap.ext
  intro v
  rw [pow_two, Module.End.mul_apply]
  cases k with
  | inl i =>
      simpa only [TauCeti.serreRootGenerator_inl, T.rep_ι_apply,
        T.rationalSerreRepresentation_serreE, LinearMap.zero_apply] using
        mulVec_mulVec_eq_zero_of_pow_two_eq_zero (T.raisingMatrixQ_pow_two i) v
  | inr i =>
      simpa only [TauCeti.serreRootGenerator_inr, T.rep_ι_apply,
        T.rationalSerreRepresentation_serreF, LinearMap.zero_apply] using
        mulVec_mulVec_eq_zero_of_pow_two_eq_zero (T.loweringMatrixQ_pow_two i) v

/-- Every represented positive or negative Serre root generator acts nilpotently. -/
theorem isNilpotent_rep_serreRootGenerator (k : B ⊕ B) :
    IsNilpotent (T.rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
      (TauCeti.serreRootGenerator T.cartanMatrix k))) :=
  ⟨2, T.rep_serreRootGenerator_pow_two k⟩

/-! ## Stability of the coordinate lattice -/

/-- Every represented Serre root generator preserves the coordinate lattice. -/
theorem rep_serreRootGenerator_mem_lattice (k : B ⊕ B) {v : ι → ℚ}
    (hv : v ∈ TauCeti.coordinateLattice ι) :
    T.rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
      (TauCeti.serreRootGenerator T.cartanMatrix k)) v ∈ TauCeti.coordinateLattice ι := by
  rw [T.rep_ι_apply]
  cases k with
  | inl i =>
      rw [TauCeti.serreRootGenerator_inl, T.rationalSerreRepresentation_serreE, raisingMatrixQ]
      exact Matrix.intCastLieHom_mulVec_mem_coordinateLattice (T.raisingMatrix i) hv
  | inr i =>
      rw [TauCeti.serreRootGenerator_inr, T.rationalSerreRepresentation_serreF, loweringMatrixQ]
      exact Matrix.intCastLieHom_mulVec_mem_coordinateLattice (T.loweringMatrix i) hv

/-- Each standard coordinate vector is a Cartan weight vector with its weight in the table. -/
theorem isCartanWeightVector_single (a : ι) :
    TauCeti.UniversalEnvelopingAlgebra.IsCartanWeightVector
      (TauCeti.serreH ℚ T.cartanMatrix) T.rep (T.weight a) (Pi.single a 1) := by
  refine (TauCeti.UniversalEnvelopingAlgebra.isCartanWeightVector_iff
    (TauCeti.serreH ℚ T.cartanMatrix) T.rep).mpr fun i ↦ ?_
  rw [T.rep_ι_apply, T.rationalSerreRepresentation_serreH]
  ext b
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/-- Every coordinate-lattice basis vector is a Cartan weight vector with its weight in the
table. -/
theorem isCartanWeightVector_coordinateLatticeBasis (a : ι) :
    TauCeti.UniversalEnvelopingAlgebra.IsCartanWeightVector
      (TauCeti.serreH ℚ T.cartanMatrix) T.rep (T.weight a)
      ((TauCeti.coordinateLatticeBasis ι a : TauCeti.coordinateLattice ι) : ι → ℚ) := by
  rw [TauCeti.coe_coordinateLatticeBasis, Pi.basisFun_apply]
  exact T.isCartanWeightVector_single a

/-- **The coordinate lattice is admissible for the Serre Kostant form of a minuscule weight
table.** -/
theorem rep_serreKostantForm_mem_lattice
    {u : _root_.UniversalEnvelopingAlgebra ℚ (Matrix.ToLieAlgebra ℚ T.cartanMatrix)}
    (hu : u ∈ TauCeti.serreKostantForm T.cartanMatrix) {v : ι → ℚ}
    (hv : v ∈ TauCeti.coordinateLattice ι) :
    T.rep u v ∈ TauCeti.coordinateLattice ι := by
  rw [TauCeti.serreKostantForm_def] at hu
  exact TauCeti.UniversalEnvelopingAlgebra.kostantForm_apply_mem_coordinateLattice
    (TauCeti.serreRootGenerator T.cartanMatrix) (TauCeti.serreH ℚ T.cartanMatrix) T.rep
    (wt := T.weight) T.rep_serreRootGenerator_pow_two
    (fun k _ hw ↦ T.rep_serreRootGenerator_mem_lattice k hw) T.isCartanWeightVector_single hu hv

/-- The coordinate lattice is stable under the generic Kostant form built from the Serre
generators. This is the form consumed by the carrier and base-change APIs. -/
theorem rep_kostantForm_mem_lattice
    (u : _root_.UniversalEnvelopingAlgebra ℚ (Matrix.ToLieAlgebra ℚ T.cartanMatrix))
    (hu : u ∈ TauCeti.UniversalEnvelopingAlgebra.kostantForm
      (TauCeti.serreRootGenerator T.cartanMatrix) (TauCeti.serreH ℚ T.cartanMatrix))
    (v : ι → ℚ) (hv : v ∈ TauCeti.coordinateLattice ι) :
    T.rep u v ∈ TauCeti.coordinateLattice ι :=
  T.rep_serreKostantForm_mem_lattice (by
    rw [TauCeti.serreKostantForm_def]
    exact hu) hv

end TauCeti.MinusculeWeightTable
