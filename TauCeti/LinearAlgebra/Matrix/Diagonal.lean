/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `Matrix.diagonal`, `Matrix.single`, and matrix multiplication occur in the statement below.
public import Mathlib.LinearAlgebra.Matrix.Transvection

/-!
# Products of diagonal matrices and matrix units

This file records a generic matrix identity for multiplying a matrix unit on both sides by
diagonal matrices.

## Main results

* `TauCeti.diagonal_mul_single_mul_diagonal`: multiplying `Eᵢⱼ(c)` on the left and right by
  diagonal matrices rescales its entry by the corresponding diagonal coefficients.
* `TauCeti.diagonal_mul_mul_diagonal`: a matrix is fixed by two-sided multiplication with
  diagonal matrices exactly when those rescale each of its entries back to itself.
-/

public section

open Matrix

namespace TauCeti

variable {n : Type*} [DecidableEq n] [Fintype n]
variable {A : Type*} [Semiring A] {i j : n}

/-- Multiplying a matrix unit on the left and right by diagonal matrices rescales its nonzero
entry by the corresponding diagonal entries. -/
@[simp]
theorem diagonal_mul_single_mul_diagonal {v w : n → A} (c : A) :
    diagonal v * single i j c * diagonal w = single i j (v i * c * w j) := by
  ext a b
  rw [Matrix.mul_assoc]
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply]
  by_cases h : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := h
    simp [mul_assoc]
  · simp [h]

/-- **A matrix is fixed by two-sided multiplication with diagonal matrices** when those rescale
each of its entries back to itself. A congruence `D M Dᵀ = M` by a diagonal matrix is this
statement after `Matrix.diagonal_transpose`. -/
theorem diagonal_mul_mul_diagonal {v w : n → A} (M : Matrix n n A)
    (h : ∀ r c, v r * M r c * w c = M r c) :
    diagonal v * M * diagonal w = M := by
  ext r c
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  exact h r c

end TauCeti
