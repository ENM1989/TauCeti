/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.CrossProduct

/-!
# The pinned type-G2 data preserves the cross product

The four numbered simple-root points `1 + t X + t² Y` of the short-root type-`G₂` carrier and the
points of its weight torus preserve the invariant cross product, the invariant
symmetric bilinear form `gᵀ B g = B`, and the invariant dual form `g B' gᵀ = B'`, over every
commutative ring. Together with
`TauCeti.G2ShortRoot.g2SpecialIsogeny_mul`, this makes the minor formula of the special isogeny
multiplicative on the submonoid they generate, in characteristic three.

## How the verification is organised

A numbered simple-root point is a divided-power exponential `1 + t N + t² P`, and each of the two
preservation equations is a polynomial in `t` of degree four. Comparing coefficients turns it into
four identities between integer matrices, none of them involving `t`, and those are decided by
computation; `preservesCross_one_add_smul_add_smul` and `preservesDualForm_one_add_smul_add_smul` do
that comparison once and for all. The `t`-coefficient of the first is the statement that `N` acts
on the cross product as a derivation, which is what makes the exponential an automorphism.

For a torus point both equations are diagonal, and each reduces to an additive relation between
weights: the weights add along the nonzero entries of the cross product, and cancel along the
nonzero entries of the form.

## What is not here

Nothing transports the special isogeny to a group of matrix-valued points, and no identification of
the carrier built from this representation with the pinned simply connected group scheme of type
`G₂` is asserted; constructions transfer to that scheme only along such an identification. Nothing
shows that the pinned submonoid exhausts any group of points.

## Main definitions

* `TauCeti.G2ShortRoot.invariantForm`: the Gram matrix of the invariant symmetric bilinear form.
* `TauCeti.G2ShortRoot.pinnedSubmonoid`: the matrices preserving the cross product and both
  forms.

## Main results

* `TauCeti.G2ShortRoot.preservesCross_one_add_smul_add_smul` and
  `TauCeti.G2ShortRoot.preservesDualForm_one_add_smul_add_smul`: the coefficient criteria for a
  divided-power exponential.
* `TauCeti.G2ShortRoot.coe_rootSubgroupPoints_mem_pinnedSubmonoid` and
  `TauCeti.G2ShortRoot.weightTorusMatrix_mem_pinnedSubmonoid`: the pinned generators lie in the
  submonoid.
* `TauCeti.G2ShortRoot.g2SpecialIsogeny_mul_of_mem_pinnedSubmonoid`: multiplicativity of the
  special isogeny there, in characteristic three.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§4.4, 12.3 and 13.4.
* S. Garibaldi and R. M. Guralnick, *Simple groups stabilizing polynomials*, Forum of Mathematics
  Pi **3** (2015), §6.
-/

public section

open Matrix

universe u

namespace TauCeti.G2ShortRoot

variable {R : Type u} [CommRing R]

/-- Coercing a sum of integer multiples of the cross-product operators. -/
private theorem map_sum_smul_crossOperator (M : Matrix (Fin 7) (Fin 7) ℤ) (k : Fin 7) :
    (∑ a, M a k • crossOperator a).map (Int.cast : ℤ → R) =
      ∑ a, ((M a k : ℤ) : R) • (crossOperator a).map (Int.cast : ℤ → R) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Int.cast_sum,
    Int.cast_mul]

/-- The Gram matrix, in the weight basis, of the invariant symmetric bilinear form of the
seven-dimensional module: the form is `uᵀ * invariantForm * v`, and a matrix preserves it when
`gᵀ * invariantForm * g = invariantForm`. It pairs the coordinate of a weight with the coordinate
of its negative, and is taken primitive over the integers. -/
@[expose] def invariantForm : Matrix (Fin 7) (Fin 7) ℤ :=
  !![0, 0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, -1, 0;
     0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, -2, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0;
     0, -1, 0, 0, 0, 0, 0;
     1, 0, 0, 0, 0, 0, 0]

/-- **The invariant form and the invariant dual form are inverse to one another up to the factor
two.** Consequently, for an invertible matrix the two preservation equations
`gᵀ * invariantForm * g = invariantForm` and
`g * invariantDualForm * gᵀ = invariantDualForm` say the same thing whenever two is a unit; the
second is the one the congruence form of the special isogeny consumes, and it does not assume
invertibility. -/
theorem invariantForm_mul_invariantDualForm :
    invariantForm * invariantDualForm = (2 : ℤ) • (1 : Matrix (Fin 7) (Fin 7) ℤ) := by
  decide +kernel

private theorem map_intCast_mul (M M' : Matrix (Fin 7) (Fin 7) ℤ) :
    (M * M').map (Int.cast : ℤ → R) = M.map (Int.cast : ℤ → R) * M'.map (Int.cast : ℤ → R) :=
  Matrix.map_mul (f := (Int.castRingHom R))

private theorem map_intCast_add (M M' : Matrix (Fin 7) (Fin 7) ℤ) :
    (M + M').map (Int.cast : ℤ → R) = M.map (Int.cast : ℤ → R) + M'.map (Int.cast : ℤ → R) := by
  ext i j; simp [Matrix.map_apply]

private theorem map_intCast_zero : (0 : Matrix (Fin 7) (Fin 7) ℤ).map (Int.cast : ℤ → R) = 0 := by
  ext i j; simp [Matrix.map_apply]

private theorem map_intCast_transpose (M : Matrix (Fin 7) (Fin 7) ℤ) :
    (M.map (Int.cast : ℤ → R))ᵀ = (Mᵀ).map (Int.cast : ℤ → R) := by
  ext i j; simp [Matrix.map_apply, Matrix.transpose_apply]

private theorem expand_congruence (t : R) (Nm Pm Cm Nm' Pm' : Matrix (Fin 7) (Fin 7) R) :
    (1 + t • Nm + t ^ 2 • Pm) * Cm * (1 + t • Nm' + t ^ 2 • Pm') =
      Cm + t • (Nm * Cm + Cm * Nm') + t ^ 2 • (Pm * Cm + Nm * Cm * Nm' + Cm * Pm') +
        t ^ 3 • (Pm * Cm * Nm' + Nm * Cm * Pm') + t ^ 4 • (Pm * Cm * Pm') := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, mul_one, one_mul,
    smul_smul, smul_add]
  module

/-- **A divided-power exponential preserves the cross product.** If a nilpotent integral matrix `N`
acts on the cross-product operators as a derivation, and its divided square `P` carries the second
and higher terms of the expansion, then `1 + t N + t² P` is multiplicative for the cross product
over every commutative ring. The four hypotheses are the coefficients of `t`, `t²`, `t³` and `t⁴`
in the expansion of the multiplicativity equation. -/
theorem preservesCross_one_add_smul_add_smul {N P : Matrix (Fin 7) (Fin 7) ℤ}
    (h1 : ∀ k, N * crossOperator k = (∑ a, N a k • crossOperator a) + crossOperator k * N)
    (h2 : ∀ k, P * crossOperator k = (∑ a, P a k • crossOperator a)
      + (∑ a, N a k • crossOperator a) * N + crossOperator k * P)
    (h3 : ∀ k, (∑ a, P a k • crossOperator a) * N + (∑ a, N a k • crossOperator a) * P = 0)
    (h4 : ∀ k, (∑ a, P a k • crossOperator a) * P = 0)
    (t : R) :
    PreservesCross
      (1 + t • N.map (Int.cast : ℤ → R) + t ^ 2 • P.map (Int.cast : ℤ → R)) := by
  rw [preservesCross_def]
  intro k
  set Nm : Matrix (Fin 7) (Fin 7) R := N.map (Int.cast : ℤ → R) with hNm
  set Pm : Matrix (Fin 7) (Fin 7) R := P.map (Int.cast : ℤ → R) with hPm
  set Xm : Fin 7 → Matrix (Fin 7) (Fin 7) R :=
    fun a => (crossOperator a).map (Int.cast : ℤ → R) with hXm
  set A : Matrix (Fin 7) (Fin 7) R := ∑ a, ((N a k : ℤ) : R) • Xm a with hA
  set B : Matrix (Fin 7) (Fin 7) R := ∑ a, ((P a k : ℤ) : R) • Xm a with hB
  have h1R : Nm * Xm k = A + Xm k * Nm := by
    have := congrArg (fun M : Matrix (Fin 7) (Fin 7) ℤ => M.map (Int.cast : ℤ → R)) (h1 k)
    simpa only [map_intCast_mul, map_intCast_add, map_sum_smul_crossOperator, hNm, hPm, hXm,
      hA] using this
  have h2R : Pm * Xm k = B + A * Nm + Xm k * Pm := by
    have := congrArg (fun M : Matrix (Fin 7) (Fin 7) ℤ => M.map (Int.cast : ℤ → R)) (h2 k)
    simpa only [map_intCast_mul, map_intCast_add, map_sum_smul_crossOperator, hNm, hPm, hXm, hA,
      hB] using this
  have h3R : B * Nm + A * Pm = 0 := by
    have := congrArg (fun M : Matrix (Fin 7) (Fin 7) ℤ => M.map (Int.cast : ℤ → R)) (h3 k)
    simpa only [map_intCast_mul, map_intCast_add, map_sum_smul_crossOperator, hNm, hPm, hXm, hA, hB,
      map_intCast_zero] using this
  have h4R : B * Pm = 0 := by
    have := congrArg (fun M : Matrix (Fin 7) (Fin 7) ℤ => M.map (Int.cast : ℤ → R)) (h4 k)
    simpa only [map_intCast_mul, map_intCast_add, map_sum_smul_crossOperator, hPm, hXm, hB,
      map_intCast_zero] using this
  have hsum : ∑ a, (1 + t • Nm + t ^ 2 • Pm) a k • Xm a = Xm k + t • A + t ^ 2 • B := by
    have hentry : ∀ a : Fin 7, (1 + t • Nm + t ^ 2 • Pm) a k =
        (if a = k then (1 : R) else 0) + t * ((N a k : ℤ) : R) + t ^ 2 * ((P a k : ℤ) : R) := by
      intro a
      simp [Matrix.one_apply, hNm, hPm, Matrix.map_apply]
    calc ∑ a, (1 + t • Nm + t ^ 2 • Pm) a k • Xm a
        = ∑ a, ((if a = k then (1 : R) else 0) • Xm a + (t * ((N a k : ℤ) : R)) • Xm a +
            (t ^ 2 * ((P a k : ℤ) : R)) • Xm a) := by
          exact Finset.sum_congr rfl fun a _ => by rw [hentry a, add_smul, add_smul]
      _ = Xm k + t • A + t ^ 2 • B := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hA, hB, Finset.smul_sum,
            Finset.smul_sum]
          congr 1
          · congr 1
            · simp
            · exact Finset.sum_congr rfl fun a _ => by rw [mul_smul]
          · exact Finset.sum_congr rfl fun a _ => by rw [mul_smul]
  rw [hsum]
  have expandL : (1 + t • Nm + t ^ 2 • Pm) * Xm k =
      Xm k + t • (Nm * Xm k) + t ^ 2 • (Pm * Xm k) := by
    rw [Matrix.add_mul, Matrix.add_mul, one_mul, Matrix.smul_mul, Matrix.smul_mul]
  have expandR : (Xm k + t • A + t ^ 2 • B) * (1 + t • Nm + t ^ 2 • Pm) =
      Xm k + t • (A + Xm k * Nm) + t ^ 2 • (B + A * Nm + Xm k * Pm) +
        t ^ 3 • (B * Nm + A * Pm) + t ^ 4 • (B * Pm) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, mul_one,
      smul_smul, smul_add]
    module
  rw [expandL, expandR, h1R, h2R, h3R, h4R, smul_zero, smul_zero, add_zero, add_zero]

/-- **Every numbered simple-root point of the carrier preserves the cross product**, over every
commutative ring. -/
theorem preservesCross_coe_rootSubgroupPoints (k : Fin 2 ⊕ Fin 2) (u : Multiplicative R) :
    PreservesCross ((rootSubgroupPoints k R u :
      _root_.Matrix.GeneralLinearGroup (Fin 7) R) : Matrix (Fin 7) (Fin 7) R) := by
  rw [coe_rootSubgroupPoints]
  refine preservesCross_one_add_smul_add_smul ?_ ?_ ?_ ?_ (Multiplicative.toAdd u) <;>
    (rcases k with i | i <;> fin_cases i <;>
      simp only [Fin.zero_eta, Fin.mk_one, rootIntMatrix_inl, rootIntMatrix_inr,
        rootDividedSquare_inl, rootDividedSquare_inr] <;>
      decide +kernel)

/-- **A divided-power exponential preserves the invariant symmetric form**, under the four
coefficient conditions on the nilpotent matrix `N` and its divided square `P`. -/
theorem preservesDualForm_one_add_smul_add_smul {N P : Matrix (Fin 7) (Fin 7) ℤ}
    (h1 : N * invariantDualForm + invariantDualForm * Nᵀ = 0)
    (h2 : P * invariantDualForm + N * invariantDualForm * Nᵀ + invariantDualForm * Pᵀ = 0)
    (h3 : P * invariantDualForm * Nᵀ + N * invariantDualForm * Pᵀ = 0)
    (h4 : P * invariantDualForm * Pᵀ = 0)
    (t : R) :
    (1 + t • N.map (Int.cast : ℤ → R) + t ^ 2 • P.map (Int.cast : ℤ → R)) *
        invariantDualForm.map (Int.cast : ℤ → R) *
        (1 + t • N.map (Int.cast : ℤ → R) + t ^ 2 • P.map (Int.cast : ℤ → R))ᵀ =
      invariantDualForm.map (Int.cast : ℤ → R) := by
  have h1R := congrArg (fun M : Matrix (Fin 7) (Fin 7) ℤ => M.map (Int.cast : ℤ → R)) h1
  have h2R := congrArg (fun M : Matrix (Fin 7) (Fin 7) ℤ => M.map (Int.cast : ℤ → R)) h2
  have h3R := congrArg (fun M : Matrix (Fin 7) (Fin 7) ℤ => M.map (Int.cast : ℤ → R)) h3
  have h4R := congrArg (fun M : Matrix (Fin 7) (Fin 7) ℤ => M.map (Int.cast : ℤ → R)) h4
  simp only [map_intCast_mul, map_intCast_add, map_intCast_zero, ← map_intCast_transpose]
    at h1R h2R h3R h4R
  rw [Matrix.transpose_add, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul,
    Matrix.transpose_smul]
  rw [expand_congruence, h1R, h2R, h3R, h4R, smul_zero, smul_zero, smul_zero, smul_zero,
    add_zero, add_zero, add_zero, add_zero]

/-- **A divided-power exponential preserves the invariant symmetric form**, under the four
coefficient conditions on the nilpotent matrix `N` and its divided square `P`. -/
theorem preservesForm_one_add_smul_add_smul {N P : Matrix (Fin 7) (Fin 7) ℤ}
    (h1 : Nᵀ * invariantForm + invariantForm * N = 0)
    (h2 : Pᵀ * invariantForm + Nᵀ * invariantForm * N + invariantForm * P = 0)
    (h3 : Pᵀ * invariantForm * N + Nᵀ * invariantForm * P = 0)
    (h4 : Pᵀ * invariantForm * P = 0)
    (t : R) :
    (1 + t • N.map (Int.cast : ℤ → R) + t ^ 2 • P.map (Int.cast : ℤ → R))ᵀ *
        invariantForm.map (Int.cast : ℤ → R) *
        (1 + t • N.map (Int.cast : ℤ → R) + t ^ 2 • P.map (Int.cast : ℤ → R)) =
      invariantForm.map (Int.cast : ℤ → R) := by
  have h1R := congrArg (fun M : Matrix (Fin 7) (Fin 7) ℤ => M.map (Int.cast : ℤ → R)) h1
  have h2R := congrArg (fun M : Matrix (Fin 7) (Fin 7) ℤ => M.map (Int.cast : ℤ → R)) h2
  have h3R := congrArg (fun M : Matrix (Fin 7) (Fin 7) ℤ => M.map (Int.cast : ℤ → R)) h3
  have h4R := congrArg (fun M : Matrix (Fin 7) (Fin 7) ℤ => M.map (Int.cast : ℤ → R)) h4
  simp only [map_intCast_mul, map_intCast_add, map_intCast_zero, ← map_intCast_transpose]
    at h1R h2R h3R h4R
  rw [Matrix.transpose_add, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul,
    Matrix.transpose_smul, expand_congruence, h1R, h2R, h3R, h4R, smul_zero, smul_zero, smul_zero,
    smul_zero, add_zero, add_zero, add_zero, add_zero]

/-- **Every numbered simple-root point of the carrier preserves the invariant symmetric form**,
over every commutative ring. -/
theorem preservesForm_coe_rootSubgroupPoints (k : Fin 2 ⊕ Fin 2) (u : Multiplicative R) :
    (((rootSubgroupPoints k R u : _root_.Matrix.GeneralLinearGroup (Fin 7) R) :
          Matrix (Fin 7) (Fin 7) R))ᵀ * invariantForm.map (Int.cast : ℤ → R) *
        ((rootSubgroupPoints k R u : _root_.Matrix.GeneralLinearGroup (Fin 7) R) :
          Matrix (Fin 7) (Fin 7) R) =
      invariantForm.map (Int.cast : ℤ → R) := by
  rw [coe_rootSubgroupPoints]
  refine preservesForm_one_add_smul_add_smul ?_ ?_ ?_ ?_ (Multiplicative.toAdd u) <;>
    (rcases k with i | i <;> fin_cases i <;>
      simp only [Fin.zero_eta, Fin.mk_one, rootIntMatrix_inl, rootIntMatrix_inr,
        rootDividedSquare_inl, rootDividedSquare_inr] <;>
      decide +kernel)

/-- **Every numbered simple-root point of the carrier fixes the invariant dual form by
congruence**, over every commutative ring. -/
theorem preservesDualForm_coe_rootSubgroupPoints (k : Fin 2 ⊕ Fin 2) (u : Multiplicative R) :
    ((rootSubgroupPoints k R u : _root_.Matrix.GeneralLinearGroup (Fin 7) R) :
          Matrix (Fin 7) (Fin 7) R) * invariantDualForm.map (Int.cast : ℤ → R) *
        (((rootSubgroupPoints k R u : _root_.Matrix.GeneralLinearGroup (Fin 7) R) :
          Matrix (Fin 7) (Fin 7) R))ᵀ =
      invariantDualForm.map (Int.cast : ℤ → R) := by
  rw [coe_rootSubgroupPoints]
  refine preservesDualForm_one_add_smul_add_smul ?_ ?_ ?_ ?_ (Multiplicative.toAdd u) <;>
    (rcases k with i | i <;> fin_cases i <;>
      simp only [Fin.zero_eta, Fin.mk_one, rootIntMatrix_inl, rootIntMatrix_inr,
        rootDividedSquare_inl, rootDividedSquare_inr] <;>
      decide +kernel)

/-- **A diagonal matrix preserves the cross product** when its entries are multiplicative along
every nonzero entry of the cross-product operators. -/
theorem preservesCross_diagonal {d : Fin 7 → R}
    (hd : ∀ k m n : Fin 7, crossOperator k m n ≠ 0 → d m = d k * d n) :
    PreservesCross (Matrix.diagonal d) := by
  rw [preservesCross_def]
  intro k
  have hsum : ∑ a, (Matrix.diagonal d) a k • (crossOperator a).map (Int.cast : ℤ → R) =
      d k • (crossOperator k).map (Int.cast : ℤ → R) := by
    rw [Finset.sum_eq_single k]
    · rw [Matrix.diagonal_apply_eq]
    · exact fun b _ hb => by rw [Matrix.diagonal_apply_ne _ hb, zero_smul]
    · exact fun hk => absurd (Finset.mem_univ k) hk
  rw [hsum]
  ext m n
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul, Matrix.map_apply]
  by_cases hz : crossOperator k m n = 0
  · rw [hz]; simp
  · rw [hd k m n hz]; ring

/-- **A diagonal matrix fixes a constant integral matrix under congruence from both sides** when
its entries are inverse to one another along every nonzero entry of that matrix. -/
theorem diagonal_mul_mul_diagonal {d : Fin 7 → R} {M : Matrix (Fin 7) (Fin 7) ℤ}
    (hd : ∀ m n : Fin 7, M m n ≠ 0 → d m * d n = 1) :
    Matrix.diagonal d * M.map (Int.cast : ℤ → R) * Matrix.diagonal d =
      M.map (Int.cast : ℤ → R) := by
  ext m n
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply]
  by_cases hz : M m n = 0
  · rw [hz]; simp
  · calc d m * ((M m n : ℤ) : R) * d n = d m * d n * ((M m n : ℤ) : R) := by ring
      _ = ((M m n : ℤ) : R) := by rw [hd m n hz, one_mul]

/-- **A diagonal matrix preserves the invariant symmetric form** when its entries are inverse to
one another along every nonzero entry of the form. -/
theorem preservesForm_diagonal {d : Fin 7 → R}
    (hd : ∀ m n : Fin 7, invariantForm m n ≠ 0 → d m * d n = 1) :
    (Matrix.diagonal d)ᵀ * invariantForm.map (Int.cast : ℤ → R) * Matrix.diagonal d =
      invariantForm.map (Int.cast : ℤ → R) := by
  rw [Matrix.diagonal_transpose]
  exact diagonal_mul_mul_diagonal hd

/-- **A diagonal matrix fixes the invariant dual form by congruence** when its entries are inverse
to one another along every nonzero entry of that form. -/
theorem preservesDualForm_diagonal {d : Fin 7 → R}
    (hd : ∀ m n : Fin 7, invariantDualForm m n ≠ 0 → d m * d n = 1) :
    Matrix.diagonal d * invariantDualForm.map (Int.cast : ℤ → R) * (Matrix.diagonal d)ᵀ =
      invariantDualForm.map (Int.cast : ℤ → R) := by
  rw [Matrix.diagonal_transpose]
  exact diagonal_mul_mul_diagonal hd

/-- **Every point of the weight torus preserves the cross product**: the weights add along the
nonzero entries of the cross-product operators. -/
theorem preservesCross_weightTorusMatrix (s : Fin 2 → Rˣ) :
    PreservesCross (Matrix.diagonal fun a => (torusCharacter s (weight a) : R)) := by
  have key : ∀ p : Fin 7 × Fin 7 × Fin 7, crossOperator p.1 p.2.1 p.2.2 = 0 ∨
      (weight p.2.1 0 = weight p.1 0 + weight p.2.2 0 ∧
        weight p.2.1 1 = weight p.1 1 + weight p.2.2 1) := by
    simp only [weight]
    decide +kernel
  refine preservesCross_diagonal fun k m n hz => ?_
  obtain ⟨hw0, hw1⟩ := (key (k, m, n)).resolve_left hz
  have hw : weight m = weight k + weight n := by
    funext j
    fin_cases j
    · exact hw0
    · exact hw1
  rw [hw, torusCharacter_add, Units.val_mul]

/-- The weight characters at a pair of indices whose weights cancel are inverse to one another. -/
private theorem torusCharacter_mul_eq_one {M : Matrix (Fin 7) (Fin 7) ℤ}
    (hM : ∀ p : Fin 7 × Fin 7, M p.1 p.2 = 0 ∨
      (weight p.1 0 + weight p.2 0 = 0 ∧ weight p.1 1 + weight p.2 1 = 0))
    (s : Fin 2 → Rˣ) (m n : Fin 7) (hz : M m n ≠ 0) :
    (torusCharacter s (weight m) : R) * (torusCharacter s (weight n) : R) = 1 := by
  obtain ⟨hw0, hw1⟩ := (hM (m, n)).resolve_left hz
  have hw : weight m + weight n = 0 := by
    funext j
    fin_cases j
    · exact hw0
    · exact hw1
  rw [← Units.val_mul, ← torusCharacter_add, hw, torusCharacter_zero, Units.val_one]

/-- **Every point of the weight torus preserves the invariant symmetric form**: the weights cancel
along the nonzero entries of the form. -/
theorem preservesForm_weightTorusMatrix (s : Fin 2 → Rˣ) :
    (Matrix.diagonal fun a => (torusCharacter s (weight a) : R))ᵀ *
        invariantForm.map (Int.cast : ℤ → R) *
        Matrix.diagonal (fun a => (torusCharacter s (weight a) : R)) =
      invariantForm.map (Int.cast : ℤ → R) :=
  preservesForm_diagonal (torusCharacter_mul_eq_one (by simp only [weight]; decide +kernel) s)

/-- **Every point of the weight torus fixes the invariant dual form by congruence**: the weights
cancel along the nonzero entries of that form. -/
theorem preservesDualForm_weightTorusMatrix (s : Fin 2 → Rˣ) :
    Matrix.diagonal (fun a => (torusCharacter s (weight a) : R)) *
        invariantDualForm.map (Int.cast : ℤ → R) *
        (Matrix.diagonal fun a => (torusCharacter s (weight a) : R))ᵀ =
      invariantDualForm.map (Int.cast : ℤ → R) :=
  preservesDualForm_diagonal (torusCharacter_mul_eq_one (by simp only [weight]; decide +kernel) s)

/-- The submonoid of matrices preserving the type-`G₂` cross product, the invariant symmetric
bilinear form, and the invariant dual form. The pinned data of the seven-dimensional module lies in
it, and in characteristic three the special isogeny is multiplicative on it: the congruence
condition on the dual form is the one that multiplicativity consumes, while the condition on the
form is the usual invariance of the bilinear form. -/
def pinnedSubmonoid : Submonoid (Matrix (Fin 7) (Fin 7) R) where
  carrier := {g | PreservesCross g ∧
    gᵀ * invariantForm.map (Int.cast : ℤ → R) * g = invariantForm.map (Int.cast : ℤ → R) ∧
    g * invariantDualForm.map (Int.cast : ℤ → R) * gᵀ =
      invariantDualForm.map (Int.cast : ℤ → R)}
  one_mem' := ⟨preservesCross_one, by simp, by simp⟩
  mul_mem' := fun {g h} hg hh =>
    ⟨hg.1.mul hh.1, by
        rw [Matrix.transpose_mul,
          show hᵀ * gᵀ * invariantForm.map (Int.cast : ℤ → R) * (g * h) =
            hᵀ * (gᵀ * invariantForm.map (Int.cast : ℤ → R) * g) * h by noncomm_ring,
          hg.2.1, hh.2.1],
      by
        rw [Matrix.transpose_mul,
          show g * h * invariantDualForm.map (Int.cast : ℤ → R) * (hᵀ * gᵀ) =
            g * (h * invariantDualForm.map (Int.cast : ℤ → R) * hᵀ) * gᵀ by noncomm_ring,
          hh.2.2, hg.2.2]⟩

/-- The three defining conditions of the pinned submonoid. -/
theorem mem_pinnedSubmonoid {g : Matrix (Fin 7) (Fin 7) R} :
    g ∈ pinnedSubmonoid ↔ PreservesCross g ∧
      gᵀ * invariantForm.map (Int.cast : ℤ → R) * g = invariantForm.map (Int.cast : ℤ → R) ∧
      g * invariantDualForm.map (Int.cast : ℤ → R) * gᵀ =
        invariantDualForm.map (Int.cast : ℤ → R) :=
  Iff.rfl

/-- Every numbered simple-root point of the carrier lies in the pinned submonoid. -/
theorem coe_rootSubgroupPoints_mem_pinnedSubmonoid (k : Fin 2 ⊕ Fin 2) (u : Multiplicative R) :
    ((rootSubgroupPoints k R u : _root_.Matrix.GeneralLinearGroup (Fin 7) R) :
      Matrix (Fin 7) (Fin 7) R) ∈ pinnedSubmonoid :=
  ⟨preservesCross_coe_rootSubgroupPoints k u, preservesForm_coe_rootSubgroupPoints k u,
    preservesDualForm_coe_rootSubgroupPoints k u⟩

/-- Every point of the weight torus lies in the pinned submonoid. -/
theorem weightTorusMatrix_mem_pinnedSubmonoid (s : Fin 2 → Rˣ) :
    (Matrix.diagonal fun a => (torusCharacter s (weight a) : R)) ∈ pinnedSubmonoid :=
  ⟨preservesCross_weightTorusMatrix s, preservesForm_weightTorusMatrix s,
    preservesDualForm_weightTorusMatrix s⟩

/-- **The special isogeny is multiplicative on the pinned submonoid** in characteristic three. -/
theorem g2SpecialIsogeny_mul_of_mem_pinnedSubmonoid [CharP R 3]
    {g h : Matrix (Fin 7) (Fin 7) R} (hg : g ∈ pinnedSubmonoid) (hh : h ∈ pinnedSubmonoid) :
    g2SpecialIsogeny (g * h) = g2SpecialIsogeny g * g2SpecialIsogeny h :=
  g2SpecialIsogeny_mul hg.1 hg.2.2 hh.1

end TauCeti.G2ShortRoot
