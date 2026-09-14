/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.SpecialIsogeny

/-!
# The type-G2 cross product and multiplicativity of the special isogeny

The seven-dimensional module of type `G₂` carries an invariant alternating multiplication, the
*cross product*, together with an invariant symmetric bilinear form. This file writes down the
cross product and the invariant form of the dual module in the weight basis of
`TauCeti.Algebra.Lie.G2.ShortRoot.Basic`, and proves that the minor formula
`Matrix.g2SpecialIsogeny` preserves products of matrices preserving both, in characteristic three.

The dual form is the one that appears, because the formula transports alternating matrices by
congruence `W ↦ g W gᵀ`: what the argument needs is the matrix `B` with `g B gᵀ = B`, which is the
Gram matrix of the induced form on the dual module, not of the form on the module itself. For an
invertible `g` the two conditions are equivalent, since `gᵀ G g = G` is the same as `g G⁻¹ gᵀ =
G⁻¹`; the congruence form is stated because it is what the proof uses and because it does not
assume invertibility.

## Why the two preservation hypotheses

Read on alternating matrices, congruence `W ↦ g W gᵀ` is the exterior square of `g`, and the
`(i, j)` entry of `Matrix.g2SpecialIsogeny g` is a fixed linear functional applied to the
congruence transform of a fixed alternating matrix. Multiplicativity therefore asks that the
seven alternating matrices `isogenySource` and the seven functionals `isogenyProjection` split a
`g`-stable subspace of the alternating matrices.

That subspace is the copy of the Lie algebra: the kernel of the contraction against the cross
product, which is stable exactly because `g` preserves the cross product. Inside it, the kernel of
the seven functionals is the short-root ideal, spanned by the alternating matrices
`crossBivector`, which in characteristic three is again stable, because `g` preserves the invariant
form as well. The splitting is the content of
`TauCeti.G2ShortRoot.eq_sum_isogenySource_add_sum_crossBivector`, and it holds only in
characteristic three: that is where the short-root vectors span an ideal and where the seven
matrices `crossBivector` fall into the kernel of the contraction.

Multiplicativity fails on the whole of `GL₇`, so the hypotheses cannot be dropped.

## What is not here

Nothing below verifies the two preservation hypotheses for the numbered simple root elements or
for the weight torus, and nothing transports the minor formula to a group of matrix-valued points:
the carrier built from this representation is not identified with the pinned simply connected
group scheme of type `G₂`, and constructions transfer to that scheme only along such an
identification. No fixed-point subgroup is formed and no finiteness or simplicity is claimed.

## Main definitions

* `TauCeti.G2ShortRoot.crossOperator` and `TauCeti.G2ShortRoot.invariantDualForm`: the cross
  product, and the invariant symmetric form of the dual module, in the weight basis.
* `TauCeti.G2ShortRoot.PreservesCross`: multiplicativity of a matrix for the cross product.
* `TauCeti.G2ShortRoot.crossMap`: the contraction of an alternating matrix against the cross
  product.
* `TauCeti.G2ShortRoot.isogenySource` and `TauCeti.G2ShortRoot.isogenyProjection`: the alternating
  matrices and the functionals through which the minor formula is read.
* `TauCeti.G2ShortRoot.crossBivector`: the alternating matrices spanning the short-root ideal.

## Main results

* `TauCeti.G2ShortRoot.g2SpecialIsogeny_apply_eq`: the minor formula as a functional of a
  congruence transform.
* `TauCeti.G2ShortRoot.crossMap_conj`: equivariance of the contraction.
* `TauCeti.G2ShortRoot.preservesCross_one` and `TauCeti.G2ShortRoot.PreservesCross.mul`: the
  matrices preserving the cross product are closed under multiplication and contain the identity.
* `TauCeti.G2ShortRoot.mul_crossBivector_mul_transpose`: stability of the short-root span under
  congruence.
* `TauCeti.G2ShortRoot.eq_sum_isogenySource_add_sum_crossBivector`: the splitting in
  characteristic three.
* `TauCeti.G2ShortRoot.g2SpecialIsogeny_mul`: multiplicativity of the special isogeny.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§12.3 and 13.4.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.
* S. Garibaldi and R. M. Guralnick, *Simple groups stabilizing polynomials*, Forum of Mathematics
  Pi **3** (2015), §6, for the cross product and the short-root ideal in characteristic three.
-/

public section

open Matrix

universe u

namespace TauCeti.G2ShortRoot

variable {R : Type u} [CommRing R]

/-- The seven matrices of the invariant cross product of the seven-dimensional module of type `G₂`,
in the weight basis of `TauCeti.Algebra.Lie.G2.ShortRoot.Basic`: `crossOperator k` is the operator
`v ↦ e_k × v` of the alternating multiplication the Lie algebra acts on by derivations. -/
@[expose] def crossOperator : Fin 7 → Matrix (Fin 7) (Fin 7) ℤ :=
  ![!![0, 0, 0, -2, 0, 0, 0;
      0, 0, 0, 0, -2, 0, 0;
      0, 0, 0, 0, 0, -2, 0;
      0, 0, 0, 0, 0, 0, -1;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0],
    !![0, 0, 2, 0, 0, 0, 0;
      0, 0, 0, 2, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, -1, 0;
      0, 0, 0, 0, 0, 0, -2;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0],
    !![0, -2, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 2, 0, 0, 0;
      0, 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, -2;
      0, 0, 0, 0, 0, 0, 0],
    !![2, 0, 0, 0, 0, 0, 0;
      0, -2, 0, 0, 0, 0, 0;
      0, 0, -2, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 2, 0, 0;
      0, 0, 0, 0, 0, 2, 0;
      0, 0, 0, 0, 0, 0, -2],
    !![0, 0, 0, 0, 0, 0, 0;
      2, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, -1, 0, 0, 0, 0;
      0, 0, 0, -2, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 2, 0],
    !![0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      2, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, -2, 0, 0, 0;
      0, 0, 0, 0, -2, 0, 0],
    !![0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0;
      0, 2, 0, 0, 0, 0, 0;
      0, 0, 2, 0, 0, 0, 0;
      0, 0, 0, 2, 0, 0, 0]]

/-- The Gram matrix, in the dual of the weight basis, of the invariant symmetric bilinear form
induced on the dual of the seven-dimensional module. Equivalently it is the invariant symmetric
tensor in the module tensored with itself, the inverse of the Gram matrix of the invariant form on
the module itself, taken primitive over the integers. It pairs the coordinate of a weight with the
coordinate of its negative, and a matrix preserves it by the congruence `g B gᵀ = B`. -/
@[expose] def invariantDualForm : Matrix (Fin 7) (Fin 7) ℤ :=
  !![0, 0, 0, 0, 0, 0, 2;
    0, 0, 0, 0, 0, -2, 0;
    0, 0, 0, 0, 2, 0, 0;
    0, 0, 0, -1, 0, 0, 0;
    0, 0, 2, 0, 0, 0, 0;
    0, -2, 0, 0, 0, 0, 0;
    2, 0, 0, 0, 0, 0, 0]

/-- The seven matrices `crossOperator a * invariantDualForm`. They are alternating, and in
characteristic three they span the short-root ideal of the Lie algebra, transported by the
invariant dual form into the alternating matrices. -/
@[expose] def crossBivector : Fin 7 → Matrix (Fin 7) (Fin 7) ℤ :=
  ![!![0, 0, 0, 2, 0, 0, 0;
      0, 0, -4, 0, 0, 0, 0;
      0, 4, 0, 0, 0, 0, 0;
      -2, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0],
    !![0, 0, 0, 0, 4, 0, 0;
      0, 0, 0, -2, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 2, 0, 0, 0, 0, 0;
      -4, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0],
    !![0, 0, 0, 0, 0, 4, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, -2, 0, 0, 0;
      0, 0, 2, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      -4, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0],
    !![0, 0, 0, 0, 0, 0, 4;
      0, 0, 0, 0, 0, 4, 0;
      0, 0, 0, 0, -4, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 4, 0, 0, 0, 0;
      0, -4, 0, 0, 0, 0, 0;
      -4, 0, 0, 0, 0, 0, 0],
    !![0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 4;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, -2, 0, 0;
      0, 0, 0, 2, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, -4, 0, 0, 0, 0, 0],
    !![0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 4;
      0, 0, 0, 0, 0, -2, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 2, 0, 0, 0;
      0, 0, -4, 0, 0, 0, 0],
    !![0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 2;
      0, 0, 0, 0, 0, -4, 0;
      0, 0, 0, 0, 4, 0, 0;
      0, 0, 0, -2, 0, 0, 0]]

/-- The seven alternating matrices whose congruence transforms the special isogeny reads: the
alternating matrix of the `j`-th distinguished index pair, joined at the middle index by the
alternating matrix of the pair `(2, 4)`. -/
@[expose] def isogenySource : Fin 7 → Matrix (Fin 7) (Fin 7) ℤ :=
  ![!![0, 1, 0, 0, 0, 0, 0;
      -1, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0],
    !![0, 0, 1, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      -1, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0],
    !![0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, -1, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0],
    !![0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, -1, 0, 0, 0, 0;
      0, -1, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0],
    !![0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, -1, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0],
    !![0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 1;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, -1, 0, 0],
    !![0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 1;
      0, 0, 0, 0, 0, -1, 0]]

/-- Transporting a cross-product operator by the invariant dual form gives the corresponding
alternating matrix. -/
theorem crossOperator_mul_invariantDualForm (a : Fin 7) :
    crossOperator a * invariantDualForm = crossBivector a := by
  revert a; decide +kernel

/-- A matrix **preserves the cross product** when it is multiplicative for it,
`g (u × v) = (g u) × (g v)`, written as one matrix identity for each basis vector of the first
argument. -/
def PreservesCross (g : Matrix (Fin 7) (Fin 7) R) : Prop :=
  ∀ k, g * (crossOperator k).map (Int.cast : ℤ → R) =
    (∑ a, g a k • (crossOperator a).map (Int.cast : ℤ → R)) * g

/-- The defining equations of cross-product preservation. -/
theorem preservesCross_def (g : Matrix (Fin 7) (Fin 7) R) :
    PreservesCross g ↔ ∀ k, g * (crossOperator k).map (Int.cast : ℤ → R) =
      (∑ a, g a k • (crossOperator a).map (Int.cast : ℤ → R)) * g := Iff.rfl

/-- The identity matrix preserves the cross product. -/
theorem preservesCross_one : PreservesCross (1 : Matrix (Fin 7) (Fin 7) R) := fun k => by
  rw [one_mul, mul_one, Finset.sum_eq_single k]
  · rw [Matrix.one_apply_eq, one_smul]
  · exact fun b _ hb => by rw [Matrix.one_apply_ne hb, zero_smul]
  · exact fun hk => absurd (Finset.mem_univ k) hk

/-- **Matrices preserving the cross product are closed under multiplication.** -/
theorem PreservesCross.mul {g h : Matrix (Fin 7) (Fin 7) R} (hg : PreservesCross g)
    (hh : PreservesCross h) : PreservesCross (g * h) := fun k => by
  have hsum : ∀ a : Fin 7, g * (crossOperator a).map (Int.cast : ℤ → R) * h =
      (∑ b, g b a • (crossOperator b).map (Int.cast : ℤ → R)) * (g * h) := fun a => by
    rw [hg a]; noncomm_ring
  calc g * h * (crossOperator k).map (Int.cast : ℤ → R)
      = g * ((∑ a, h a k • (crossOperator a).map (Int.cast : ℤ → R)) * h) := by
        rw [mul_assoc, hh k]
    _ = ∑ a, h a k • (g * (crossOperator a).map (Int.cast : ℤ → R) * h) := by
        rw [Finset.sum_mul, Matrix.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by
          rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
    _ = ∑ a, ∑ b, (h a k * g b a) • (crossOperator b).map (Int.cast : ℤ → R) * (g * h) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hsum a, Finset.sum_mul, Finset.smul_sum]
        exact Finset.sum_congr rfl fun b _ => by rw [Matrix.smul_mul, smul_smul, Matrix.smul_mul]
    _ = (∑ b, (g * h) b k • (crossOperator b).map (Int.cast : ℤ → R)) * (g * h) := by
        rw [Finset.sum_comm, Finset.sum_mul]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Matrix.mul_apply, ← Finset.sum_mul, ← Finset.sum_smul]
        exact congrArg (fun c : R => c • (crossOperator b).map (Int.cast : ℤ → R) * (g * h))
          (Finset.sum_congr rfl fun a _ => mul_comm _ _)

/-- **The span of the alternating matrices `crossBivector` is stable under congruence.** A matrix
preserving the cross product and fixing the invariant dual form by congruence permutes them
through the tautological action on their index. -/
theorem mul_crossBivector_mul_transpose {g : Matrix (Fin 7) (Fin 7) R} (hg : PreservesCross g)
    (hB : g * invariantDualForm.map (Int.cast : ℤ → R) * gᵀ =
      invariantDualForm.map (Int.cast : ℤ → R))
    (k : Fin 7) :
    g * (crossBivector k).map (Int.cast : ℤ → R) * gᵀ =
      ∑ a, g a k • (crossBivector a).map (Int.cast : ℤ → R) := by
  have hmap : ∀ a : Fin 7, (crossBivector a).map (Int.cast : ℤ → R) =
      (crossOperator a).map (Int.cast : ℤ → R) * invariantDualForm.map (Int.cast : ℤ → R) :=
      fun a => by
    rw [← crossOperator_mul_invariantDualForm a]
    exact Matrix.map_mul (f := (Int.castRingHom R))
  calc g * (crossBivector k).map (Int.cast : ℤ → R) * gᵀ
      = (g * (crossOperator k).map (Int.cast : ℤ → R)) *
          invariantDualForm.map (Int.cast : ℤ → R) * gᵀ := by rw [hmap k]; noncomm_ring
    _ = (∑ a, g a k • (crossOperator a).map (Int.cast : ℤ → R)) *
          (g * invariantDualForm.map (Int.cast : ℤ → R) * gᵀ) := by rw [hg k]; noncomm_ring
    _ = ∑ a, g a k • (crossBivector a).map (Int.cast : ℤ → R) := by
        rw [hB, Finset.sum_mul]
        exact Finset.sum_congr rfl fun a _ => by rw [smul_mul_assoc, hmap a]

/-- The cross product contracted against a matrix: the `m`-th coordinate of `crossMap W` pairs `W`
with the `m`-th row of the cross-product operators. On alternating matrices this is the cross
product itself, read as a linear map to the module. -/
def crossMap (W : Matrix (Fin 7) (Fin 7) R) (m : Fin 7) : R :=
  ∑ k, ((crossOperator k).map (Int.cast : ℤ → R) * Wᵀ) m k

/-- The defining formula of the contraction. -/
theorem crossMap_def (W : Matrix (Fin 7) (Fin 7) R) (m : Fin 7) :
    crossMap W m = ∑ k, ((crossOperator k).map (Int.cast : ℤ → R) * Wᵀ) m k := (rfl)

/-- The contraction of an integral alternating matrix is the integer contraction, coerced. -/
theorem crossMap_map (W : Matrix (Fin 7) (Fin 7) ℤ) (m : Fin 7) :
    crossMap (W.map (Int.cast : ℤ → R)) m = ((crossMap W m : ℤ) : R) := by
  have key : ∀ k : Fin 7,
      (crossOperator k).map (Int.cast : ℤ → R) * (W.map (Int.cast : ℤ → R))ᵀ =
        ((crossOperator k).map (Int.cast : ℤ → ℤ) * Wᵀ).map (Int.cast : ℤ → R) := fun k => by
    ext a b
    simp [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Int.cast_sum]
  rw [crossMap_def, crossMap_def, Int.cast_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [key k, Matrix.map_apply]

/-- The alternating matrices read by the special isogeny lie in the kernel of the contraction, so
they lie in the Lie algebra. -/
theorem crossMap_isogenySource (j m : Fin 7) :
    crossMap ((isogenySource j).map (Int.cast : ℤ → R)) m = 0 := by
  rw [crossMap_map]
  norm_num [show ∀ j m : Fin 7, crossMap (isogenySource j) m = 0 by decide +kernel]

/-- **The contraction is equivariant.** A matrix preserving the cross product intertwines its
congruence action on alternating matrices with its tautological action on vectors. -/
theorem crossMap_conj {g : Matrix (Fin 7) (Fin 7) R} (hg : PreservesCross g)
    (W : Matrix (Fin 7) (Fin 7) R) (m : Fin 7) :
    crossMap (g * W * gᵀ) m = ∑ c, g m c * crossMap W c := by
  have hT : (g * W * gᵀ)ᵀ = g * Wᵀ * gᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
    noncomm_ring
  have hL : ∀ k : Fin 7,
      ((crossOperator k).map (Int.cast : ℤ → R) * (g * Wᵀ * gᵀ)) m k =
        ∑ a, ((crossOperator k).map (Int.cast : ℤ → R) * g * Wᵀ) m a * g k a := fun k => by
    rw [show (crossOperator k).map (Int.cast : ℤ → R) * (g * Wᵀ * gᵀ) =
      ((crossOperator k).map (Int.cast : ℤ → R) * g * Wᵀ) * gᵀ by noncomm_ring, Matrix.mul_apply]
    rfl
  have step : ∀ a : Fin 7,
      ∑ k, ((crossOperator k).map (Int.cast : ℤ → R) * g * Wᵀ) m a * g k a =
        ∑ c, g m c * ((crossOperator a).map (Int.cast : ℤ → R) * Wᵀ) c a := fun a => by
    have h1 : ∑ k, ((crossOperator k).map (Int.cast : ℤ → R) * g * Wᵀ) m a * g k a =
        ((∑ k, g k a • (crossOperator k).map (Int.cast : ℤ → R)) * g * Wᵀ) m a := by
      rw [Finset.sum_mul, Finset.sum_mul, Matrix.sum_apply]
      exact Finset.sum_congr rfl fun k _ => by
        rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, mul_comm]
    have h2 : ∑ c, g m c * ((crossOperator a).map (Int.cast : ℤ → R) * Wᵀ) c a =
        (g * ((crossOperator a).map (Int.cast : ℤ → R) * Wᵀ)) m a := Matrix.mul_apply.symm
    rw [h1, h2, show (∑ k, g k a • (crossOperator k).map (Int.cast : ℤ → R)) * g * Wᵀ =
      ((∑ k, g k a • (crossOperator k).map (Int.cast : ℤ → R)) * g) * Wᵀ from rfl, ← hg a]
    noncomm_ring
  calc crossMap (g * W * gᵀ) m
      = ∑ k, ∑ a, ((crossOperator k).map (Int.cast : ℤ → R) * g * Wᵀ) m a * g k a := by
        rw [crossMap_def, hT]
        exact Finset.sum_congr rfl fun k _ => hL k
    _ = ∑ a, ∑ k, ((crossOperator k).map (Int.cast : ℤ → R) * g * Wᵀ) m a * g k a :=
        Finset.sum_comm
    _ = ∑ a, ∑ c, g m c * ((crossOperator a).map (Int.cast : ℤ → R) * Wᵀ) c a :=
        Finset.sum_congr rfl fun a _ => step a
    _ = ∑ c, ∑ a, g m c * ((crossOperator a).map (Int.cast : ℤ → R) * Wᵀ) c a := Finset.sum_comm
    _ = ∑ c, g m c * crossMap W c :=
        Finset.sum_congr rfl fun c _ => by rw [crossMap_def, Finset.mul_sum]

/-- The linear functional the special isogeny reads on the `i`-th distinguished index pair: the
entry there, diminished at the middle index by the entry at the pair `(0, 6)`. -/
def isogenyProjection (i : Fin 7) : Matrix (Fin 7) (Fin 7) R →ₗ[R] R where
  toFun W := W (g2SpecialIsogenyPair i).1 (g2SpecialIsogenyPair i).2 - if i = 3 then W 0 6 else 0
  map_add' W V := by
    split_ifs <;> simp
    ring
  map_smul' c W := by
    split_ifs <;> simp [smul_eq_mul]
    ring

/-- The entrywise formula for the functional. -/
theorem isogenyProjection_apply (i : Fin 7) (W : Matrix (Fin 7) (Fin 7) R) :
    isogenyProjection i W =
      W (g2SpecialIsogenyPair i).1 (g2SpecialIsogenyPair i).2 -
        if i = 3 then W 0 6 else 0 := (rfl)

/-- The functionals and the alternating matrices `isogenySource` are dual to one another. -/
theorem isogenyProjection_isogenySource (i j : Fin 7) :
    isogenyProjection i ((isogenySource j).map (Int.cast : ℤ → R)) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [isogenyProjection_apply, isogenySource]

/-- The functionals kill the alternating matrices spanning the short-root ideal. -/
theorem isogenyProjection_crossBivector (i a : Fin 7) :
    isogenyProjection i ((crossBivector a).map (Int.cast : ℤ → R)) = 0 := by
  fin_cases i <;> fin_cases a <;> simp [isogenyProjection_apply, crossBivector]

private theorem apply_mul_isogenySource_mul_transpose (g : Matrix (Fin 7) (Fin 7) R) (j : Fin 7)
    (a b : Fin 7) :
    (g * (isogenySource j).map (Int.cast : ℤ → R) * gᵀ) a b =
      g2SpecialIsogenyColumn g (a, b) j := by
  fin_cases j <;>
    simp [g2SpecialIsogenyColumn_def, pairMinor_eq, Matrix.mul_apply, Fin.sum_univ_seven,
      isogenySource, Matrix.transpose_apply] <;> ring

/-- **The minor formula read by congruence.** The `(i, j)` entry of the special isogeny of `g` is
the `i`-th functional applied to the congruence transform by `g` of the `j`-th alternating
matrix. -/
theorem g2SpecialIsogeny_apply_eq (g : Matrix (Fin 7) (Fin 7) R) (i j : Fin 7) :
    g2SpecialIsogeny g i j =
      isogenyProjection i (g * (isogenySource j).map (Int.cast : ℤ → R) * gᵀ) := by
  rw [isogenyProjection_apply, apply_mul_isogenySource_mul_transpose, g2SpecialIsogeny_apply]
  split_ifs with h
  · rw [apply_mul_isogenySource_mul_transpose]
  · rfl

/-- The coordinates of an alternating matrix along the matrices `crossBivector`, each a single
entry up to sign. -/
@[expose] def isogenyKernelCoeff (a : Fin 7) (W : Matrix (Fin 7) (Fin 7) R) : R :=
  ![-W 1 2, W 1 3, W 2 3, W 0 6, W 3 4, W 3 5, -W 4 5] a

/-- The contraction written entrywise. -/
theorem crossMap_apply (W : Matrix (Fin 7) (Fin 7) R) (m : Fin 7) :
    crossMap W m = ∑ k, ∑ l, ((crossOperator k m l : ℤ) : R) * W k l := by
  rw [crossMap_def]
  exact Finset.sum_congr rfl fun k _ => by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun l _ => by rw [Matrix.map_apply, Matrix.transpose_apply]

/-- **The splitting of the Lie algebra in characteristic three.** An alternating matrix killed by
the cross-product contraction is the sum of its `isogenySource` part, read by the functionals
`isogenyProjection`, and its short-root part, read by the coordinates `isogenyKernelCoeff`. So in
characteristic three the alternating matrices killed by the contraction are spanned by the seven
matrices `isogenySource` together with the seven matrices `crossBivector`. -/
theorem eq_sum_isogenySource_add_sum_crossBivector [CharP R 3] {W : Matrix (Fin 7) (Fin 7) R}
    (hW : Wᵀ = -W) (hc : ∀ m, crossMap W m = 0) :
    W = (∑ k, isogenyProjection k W • (isogenySource k).map (Int.cast : ℤ → R)) +
      ∑ a, isogenyKernelCoeff a W • (crossBivector a).map (Int.cast : ℤ → R) := by
  have h3 : (3 : R) = 0 := by exact_mod_cast CharP.cast_eq_zero R 3
  have hA : ∀ a b, W a b + W b a = 0 := fun a b => by
    have h := congrFun (congrFun hW b) a
    rw [Matrix.transpose_apply, Matrix.neg_apply] at h
    rw [h]
    ring
  have e0 := (crossMap_apply W 0).symm.trans (hc 0)
  have e1 := (crossMap_apply W 1).symm.trans (hc 1)
  have e2 := (crossMap_apply W 2).symm.trans (hc 2)
  have e3 := (crossMap_apply W 3).symm.trans (hc 3)
  have e4 := (crossMap_apply W 4).symm.trans (hc 4)
  have e5 := (crossMap_apply W 5).symm.trans (hc 5)
  have e6 := (crossMap_apply W 6).symm.trans (hc 6)
  simp [Fin.sum_univ_seven, crossOperator] at e0 e1 e2 e3 e4 e5 e6
  ext m n
  fin_cases m <;> fin_cases n <;>
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Fin.sum_univ_seven, isogenyProjection_apply, isogenyKernelCoeff, isogenySource,
      crossBivector, Matrix.map_apply, g2SpecialIsogenyPair_zero, g2SpecialIsogenyPair_one,
      g2SpecialIsogenyPair_two, g2SpecialIsogenyPair_three, g2SpecialIsogenyPair_four,
      g2SpecialIsogenyPair_five, g2SpecialIsogenyPair_six, Matrix.cons_val', Matrix.cons_val,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.of_apply,
      Fin.isValue] <;>
    push_cast
  · linear_combination -hA 0 0 + (W 0 0) * h3
  · ring
  · ring
  · linear_combination -e0 - hA 0 3 + hA 1 2 + (W 1 2 - W 2 1 + W 3 0) * h3
  · linear_combination -e1 - hA 0 4 + hA 1 3 + (-W 1 3 - W 3 1 + W 4 0) * h3
  · linear_combination -e2 - hA 0 5 + hA 2 3 + (-W 2 3 - W 3 2 + W 5 0) * h3
  · linear_combination (-W 0 6) * h3
  · linear_combination hA 0 1
  · linear_combination -hA 1 1 + (W 1 1) * h3
  · linear_combination (-W 1 2) * h3
  · linear_combination (W 1 3) * h3
  · ring
  · linear_combination (-W 0 6) * h3
  · linear_combination -e4 - hA 1 6 + hA 3 4 + (-W 3 4 - W 4 3 + W 6 1) * h3
  · linear_combination hA 0 2
  · linear_combination hA 1 2 + (W 1 2) * h3
  · linear_combination -hA 2 2 + (W 2 2) * h3
  · linear_combination (W 2 3) * h3
  · linear_combination -e3 + hA 0 6 + hA 1 5 - hA 2 4 + (W 0 6 - W 1 5 + W 2 4) * h3
  · ring
  · linear_combination -e5 - hA 2 6 + hA 3 5 + (-W 3 5 - W 5 3 + W 6 2) * h3
  · linear_combination e0 - hA 0 3 - hA 1 2 + (W 0 3 - W 1 2 + W 2 1) * h3
  · linear_combination hA 1 3 + (-W 1 3) * h3
  · linear_combination hA 2 3 + (-W 2 3) * h3
  · linear_combination -hA 3 3 + (W 3 3) * h3
  · linear_combination (W 3 4) * h3
  · linear_combination (W 3 5) * h3
  · linear_combination -e6 - hA 3 6 + hA 4 5 + (W 4 5 - W 5 4 + W 6 3) * h3
  · linear_combination e1 - hA 0 4 - hA 1 3 + (W 0 4 + W 1 3 + W 3 1) * h3
  · linear_combination hA 1 4
  · linear_combination e3 - hA 0 6 - hA 1 5 - hA 2 4 + (-W 0 6 + W 1 5 + W 4 2) * h3
  · linear_combination hA 3 4 + (-W 3 4) * h3
  · linear_combination -hA 4 4 + (W 4 4) * h3
  · linear_combination (-W 4 5) * h3
  · ring
  · linear_combination e2 - hA 0 5 - hA 2 3 + (W 0 5 + W 2 3 + W 3 2) * h3
  · linear_combination hA 1 5 + (W 0 6) * h3
  · linear_combination hA 2 5
  · linear_combination hA 3 5 + (-W 3 5) * h3
  · linear_combination hA 4 5 + (W 4 5) * h3
  · linear_combination -hA 5 5 + (W 5 5) * h3
  · ring
  · linear_combination hA 0 6 + (W 0 6) * h3
  · linear_combination e4 - hA 1 6 - hA 3 4 + (W 1 6 + W 3 4 + W 4 3) * h3
  · linear_combination e5 - hA 2 6 - hA 3 5 + (W 2 6 + W 3 5 + W 5 3) * h3
  · linear_combination e6 - hA 3 6 - hA 4 5 + (W 3 6 - W 4 5 + W 5 4) * h3
  · linear_combination hA 4 6
  · linear_combination hA 5 6
  · linear_combination -hA 6 6 + (W 6 6) * h3

/-- The alternating matrices read by the special isogeny are alternating over any commutative
ring. -/
theorem transpose_isogenySource_map (l : Fin 7) :
    ((isogenySource l).map (Int.cast : ℤ → R))ᵀ = -(isogenySource l).map (Int.cast : ℤ → R) := by
  have key : ∀ l : Fin 7, (isogenySource l)ᵀ = -isogenySource l := by decide +kernel
  ext a b
  have := congrFun (congrFun (key l) a) b
  rw [Matrix.transpose_apply, Matrix.neg_apply] at this
  rw [Matrix.transpose_apply, Matrix.neg_apply, Matrix.map_apply, Matrix.map_apply, this,
    Int.cast_neg]

/-- **The special isogeny is multiplicative in characteristic three** on matrices preserving the
cross product, the left factor fixing the invariant dual form by congruence as well.
Multiplicativity
fails on the whole of `GL₇`: it is the two preservation hypotheses, which the pinned type-`G₂`
data satisfies, that make the quotient by the short-root ideal an invariant subquotient and so
turn the minor formula into a homomorphism. -/
theorem g2SpecialIsogeny_mul [CharP R 3] {g h : Matrix (Fin 7) (Fin 7) R}
    (hg : PreservesCross g)
    (hgB : g * invariantDualForm.map (Int.cast : ℤ → R) * gᵀ =
      invariantDualForm.map (Int.cast : ℤ → R))
    (hh : PreservesCross h) :
    g2SpecialIsogeny (g * h) = g2SpecialIsogeny g * g2SpecialIsogeny h := by
  have expand : ∀ (c : Fin 7 → R) (M : Fin 7 → Matrix (Fin 7) (Fin 7) R),
      g * (∑ k, c k • M k) * gᵀ = ∑ k, c k • (g * M k * gᵀ) := fun c M => by
    rw [Matrix.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by rw [Matrix.mul_smul, Matrix.smul_mul]
  ext i j
  set W : Matrix (Fin 7) (Fin 7) R := h * (isogenySource j).map (Int.cast : ℤ → R) * hᵀ
    with hWdef
  have hWanti : Wᵀ = -W := by
    rw [hWdef, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      transpose_isogenySource_map]
    simp [Matrix.mul_assoc]
  have hWcross : ∀ m, crossMap W m = 0 := fun m => by
    rw [hWdef, crossMap_conj hh]
    simp [crossMap_isogenySource]
  have hY : ∀ a : Fin 7,
      isogenyProjection i (g * (crossBivector a).map (Int.cast : ℤ → R) * gᵀ) = 0 := fun a => by
    rw [mul_crossBivector_mul_transpose hg hgB a, map_sum]
    exact Finset.sum_eq_zero fun b _ => by
      rw [map_smul, isogenyProjection_crossBivector, smul_zero]
  have h1 : g2SpecialIsogeny (g * h) i j = isogenyProjection i (g * W * gᵀ) := by
    rw [g2SpecialIsogeny_apply_eq, hWdef, Matrix.transpose_mul]
    congr 1
    noncomm_ring
  rw [h1, eq_sum_isogenySource_add_sum_crossBivector hWanti hWcross, Matrix.mul_add,
    Matrix.add_mul, map_add, expand, expand, map_sum, map_sum]
  simp only [map_smul, smul_eq_mul, hY, mul_zero, Finset.sum_const_zero, add_zero]
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← g2SpecialIsogeny_apply_eq, ← g2SpecialIsogeny_apply_eq, mul_comm]

end TauCeti.G2ShortRoot
