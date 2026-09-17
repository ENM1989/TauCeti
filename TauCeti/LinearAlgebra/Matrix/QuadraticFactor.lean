/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic.Module

/-!
# A matrix between two quadratic factors, expanded in the parameter

A divided-power exponential of a square-zero or cube-zero matrix is a quadratic polynomial
`1 + u X + u² Y` in its parameter. Placing a matrix between two such factors and collecting the
powers of the parameter is a purely algebraic expansion, with five coefficient matrices built
from the four matrices involved. It is the computation that turns a conjugation, or a congruence,
by a divided-power exponential into finitely many identities between products.

The two factors are allowed to have different linear and quadratic terms, so the same expansion
serves a conjugation, where the right factor is the inverse of the left one, and a congruence,
where it is the transpose.

## Main results

* `Matrix.mul_mul_of_one_add_smul_add_smul`: the expansion.
-/

public section

namespace Matrix

/-- **A matrix between two quadratic factors, expanded in the parameter.** -/
theorem mul_mul_of_one_add_smul_add_smul {l n R : Type*} [Fintype l] [DecidableEq l]
    [Fintype n] [DecidableEq n] [CommSemiring R]
    (X Y : Matrix l l R) (X' Y' : Matrix n n R) (M : Matrix l n R) (u : R) :
    (1 + u • X + u ^ 2 • Y) * M * (1 + u • X' + u ^ 2 • Y') =
      M + u • (X * M + M * X') + u ^ 2 • (X * M * X' + (Y * M + M * Y')) +
        u ^ 3 • (X * M * Y' + Y * M * X') + u ^ 4 • (Y * M * Y') := by
  calc
    (1 + u • X + u ^ 2 • Y) * M * (1 + u • X' + u ^ 2 • Y') =
        (M + u • (X * M) + u ^ 2 • (Y * M)) * (1 + u • X' + u ^ 2 • Y') := by
      congr 1
      rw [Matrix.add_mul, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.smul_mul]
    _ = (M + u • (X * M) + u ^ 2 • (Y * M)) +
          u • ((M + u • (X * M) + u ^ 2 • (Y * M)) * X') +
          u ^ 2 • ((M + u • (X * M) + u ^ 2 • (Y * M)) * Y') := by
      rw [Matrix.mul_add, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_smul]
    _ = M + u • (X * M + M * X') + u ^ 2 • (X * M * X' + (Y * M + M * Y')) +
        u ^ 3 • (X * M * Y' + Y * M * X') + u ^ 4 • (Y * M * Y') := by
      simp only [Matrix.add_mul, Matrix.smul_mul]
      module

end Matrix
