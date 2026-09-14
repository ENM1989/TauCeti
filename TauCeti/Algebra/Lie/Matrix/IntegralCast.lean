/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Data.Matrix.Basic
public import TauCeti.LinearAlgebra.CoordinateLattice

/-!
# Integral matrices acting on a rational coordinate space

An explicit Chevalley carrier starts from a representation of a Serre presentation by matrices
with integer entries, extends it to the rational Serre algebra, and shows that the integral
coordinate lattice of the rational module is preserved. This file collects the facts that step
needs, stated for an arbitrary index type so that every such carrier shares them.

Entrywise coercion of integer matrices is a homomorphism of Lie rings for the commutator
brackets, so it carries a Serre system over `ℤ` to one over the target ring. Two further
ingredients complete the passage: the adjoint action of a Lie algebra does not depend on the
base ring over which the algebra is read, so a higher Serre relation proved for `ad ℤ` is the
same statement as the one asked of `ad ℚ`; and a coerced integer matrix sends integral
coordinate vectors to integral coordinate vectors.

## Main declarations

* `TauCeti.matrixIntCastLieHom`: entrywise coercion of integer matrices, as a homomorphism of
  Lie rings.

## Main results

* `TauCeti.matrixIntCastLieHom_apply` and `TauCeti.matrixIntCastLieHom_mul`: the coercion acts
  entrywise and is multiplicative.
* `TauCeti.ad_pow_apply_eq_ad_pow_apply`: iterating the adjoint action gives the same element
  whichever base ring the Lie algebra is read over.
* `TauCeti.mulVec_mulVec_eq_zero_of_pow_two_eq_zero`: a square-zero matrix annihilates every
  vector in two steps.
* `TauCeti.matrixIntCastLieHom_mulVec_mem_coordinateLattice`: a coerced integer matrix preserves
  the integral coordinate lattice.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§18 and 26.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

open scoped Matrix

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Entrywise coercion of integer matrices -/

/-- Entrywise coercion of integer matrices into a commutative ring, as a homomorphism of Lie
rings for the commutator brackets. -/
noncomputable def matrixIntCastLieHom (R : Type*) [CommRing R] :
    Matrix n n ℤ →ₗ⁅ℤ⁆ Matrix n n R :=
  ((Int.castRingHom R).mapMatrix.toIntAlgHom).toLieHom

/-- Entrywise coercion of integer matrices acts on entries by the integer cast. -/
@[simp]
theorem matrixIntCastLieHom_apply (R : Type*) [CommRing R] (M : Matrix n n ℤ) (a b : n) :
    matrixIntCastLieHom R M a b = (M a b : R) := by
  simp only [matrixIntCastLieHom, AlgHom.toLieHom_apply, RingHom.toIntAlgHom_apply,
    RingHom.mapMatrix_apply, Matrix.map_apply, Int.coe_castRingHom]

/-- Entrywise coercion of integer matrices is multiplicative, being a ring homomorphism read as
a homomorphism of Lie rings. -/
@[simp]
theorem matrixIntCastLieHom_mul (R : Type*) [CommRing R] (M N : Matrix n n ℤ) :
    matrixIntCastLieHom R (M * N) = matrixIntCastLieHom R M * matrixIntCastLieHom R N := by
  ext a b
  simp only [matrixIntCastLieHom_apply, Matrix.mul_apply, Int.cast_sum, Int.cast_mul]

/-! ## Base-ring independence of the adjoint action -/

/-- **The adjoint action does not depend on the base ring.** A Lie algebra over two commutative
rings has one bracket, so iterating `ad` over either ring gives the same element. This reads a
higher Serre relation proved over `ℤ` as the relation asked of a Lie algebra over `ℚ`. -/
theorem ad_pow_apply_eq_ad_pow_apply {L : Type*} [LieRing L] (R S : Type*) [CommRing R]
    [CommRing S] [LieAlgebra R L] [LieAlgebra S L] (x y : L) (k : ℕ) :
    (LieAlgebra.ad R L x ^ k) y = (LieAlgebra.ad S L x ^ k) y := by
  induction k generalizing y with
  | zero => simp
  | succ k ih =>
      simp only [pow_succ, Module.End.mul_apply, LieAlgebra.ad_apply]
      exact ih ⁅x, y⁆

/-! ## Square-zero matrices and the coordinate lattice -/

/-- A square-zero matrix annihilates every vector in two multiplications. -/
theorem mulVec_mulVec_eq_zero_of_pow_two_eq_zero {R : Type*} [CommRing R] {M : Matrix n n R}
    (hM : M ^ 2 = 0) (v : n → R) : M *ᵥ M *ᵥ v = 0 := by
  rw [Matrix.mulVec_mulVec, ← pow_two, hM, Matrix.zero_mulVec]

/-- **A coerced integer matrix preserves the integral coordinate lattice**, each coordinate of
the image being an integer combination of the coordinates of the argument. -/
theorem matrixIntCastLieHom_mulVec_mem_coordinateLattice (M : Matrix n n ℤ) {v : n → ℚ}
    (hv : v ∈ coordinateLattice n) :
    matrixIntCastLieHom ℚ M *ᵥ v ∈ coordinateLattice n := by
  rw [mem_coordinateLattice_iff] at hv ⊢
  choose z hz using hv
  intro a
  refine ⟨∑ b, M a b * z b, ?_⟩
  simp only [Int.cast_sum, Int.cast_mul, hz, Matrix.mulVec, dotProduct,
    matrixIntCastLieHom_apply]

end TauCeti
