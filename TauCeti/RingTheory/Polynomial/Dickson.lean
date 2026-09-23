/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.RingTheory.Polynomial.Dickson
public import Mathlib.RingTheory.PowerSeries.Basic

import Mathlib.Algebra.Ring.GeomSum

/-!
# Evaluating the Dickson polynomials of the second kind

The Dickson polynomials of the second kind, `Polynomial.dickson 2 a`, obey
`dickson 2 a (n + 2) = X * dickson 2 a (n + 1) - C a * dickson 2 a n` with `dickson 2 a 0 = 1` and
`dickson 2 a 1 = X`. Evaluated at a sum `x + y` with `x * y = a`, they are the complete homogeneous
symmetric polynomials in `x` and `y`; this file proves that, and the consequences it has for the
values at `t` when `t` and `a` are the trace and determinant of a `2 × 2` matrix.

These values are the weights of the Eichler–Selberg trace formula. There, for `k ≥ 2`, the
polynomial `P_k(t, n)` is the coefficient family with generating function
`∑_{k ≥ 2} P_k(t, n) x ^ (k - 2) = (1 - t x + n x²)⁻¹`, and its coefficient recurrence is the
Dickson recurrence, so `P_k(t, n) = (dickson 2 n (k - 2)).eval t`. That is why no new polynomial
family is introduced for it: `dickson_two_eval_mul_mk_eq_one` is the generating function, and the
remaining results are the closed forms the trace formula consumes.

## Main results

* `Polynomial.dickson_two_eval_add`: if `x * y = a`, then
  `(dickson 2 a n).eval (x + y) = ∑ i ∈ range (n + 1), x ^ i * y ^ (n - i)`. For the trace `t` and
  determinant `a` of a `2 × 2` matrix with eigenvalues `x` and `y`, the right side is the trace of
  the matrix on homogeneous polynomials of degree `n`.
* `Polynomial.dickson_two_eval_add_mul_sub`: the same value times `x - y` is
  `x ^ (n + 1) - y ^ (n + 1)`: the quotient formula `(ρ ^ (k - 1) - ρ̄ ^ (k - 1)) / (ρ - ρ̄)` with
  the division cleared, so it also holds when `x = y`.
* `Polynomial.dickson_two_eval_two_mul`: at a repeated root, `t = 2 x` and `a = x ^ 2`, the value is
  `(n + 1) * x ^ n`. These are the terms with `t² = 4 a`, where the quotient formula says nothing.
* `Polynomial.dickson_two_sq_eval_mul`: `(dickson 2 (s ^ 2) n).eval (s * t)` is
  `s ^ n * (Chebyshev.S R n).eval t`, the division-free form of
  `P_k(t, s²) = s ^ (k - 2) * U_{k-2}(t / (2 s))`, from the homogeneity
  `Polynomial.dickson_two_eval_mul`.
* `Polynomial.dickson_two_eval_mul_mk_eq_one`: the generating function
  `(1 - t X + a X²) * ∑ₙ (dickson 2 a n).eval t * Xⁿ = 1`.

## References

* D. Zagier, *The Eichler–Selberg trace formula on `SL₂(ℤ)`*, appendix to S. Lang,
  *Introduction to Modular Forms*, Springer, 1976.
* A. Popa and D. Zagier, *A simple proof of the Eichler–Selberg trace formula*,
  J. Ramanujan Math. Soc. (2019), arXiv:1711.00327.
-/

public section

open Finset

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- **The Dickson polynomial of the second kind at `x + y` is the complete homogeneous symmetric
polynomial in `x` and `y`**, when its parameter is `x * y`.

When `x` and `y` are the eigenvalues of a `2 × 2` matrix, `x + y` and `x * y` are its trace and
determinant, and the right side is the trace of the matrix on homogeneous polynomials of degree
`n`; this is how the Eichler–Selberg weights enter as traces. Compare Mathlib's
`dickson_one_one_eval_add_inv`, the first-kind analogue for `x * y = 1`, where the value is the
power sum `x ^ n + y ^ n`. -/
theorem dickson_two_eval_add {x y a : R} (h : x * y = a) (n : ℕ) :
    (dickson 2 a n).eval (x + y) = ∑ i ∈ range (n + 1), x ^ i * y ^ (n - i) := by
  subst h
  induction n using Nat.twoStepInduction with
  | zero => simp [dickson_zero]; norm_num
  | one => simp [dickson_one, sum_range_succ]; ring
  | more n ih₀ ih₁ =>
    -- peel the top term off each complete homogeneous sum, `hₘ₊₁ = x ^ (m + 1) + y * hₘ`
    have peel (m : ℕ) : ∑ i ∈ range (m + 2), x ^ i * y ^ (m + 1 - i) =
        x ^ (m + 1) + y * ∑ i ∈ range (m + 1), x ^ i * y ^ (m - i) := by
      rw [geom_sum₂_succ_eq]
      simp
    rw [dickson_add_two, eval_sub, eval_mul, eval_mul, eval_X, eval_C, ih₁, ih₀, peel (n + 1),
      peel n]
    ring

/-- **The Dickson value times `x - y` is `x ^ (n + 1) - y ^ (n + 1)`**, when `x * y = a`.

This is the quotient formula `P_k(t, a) = (x ^ (k - 1) - y ^ (k - 1)) / (x - y)` for the roots `x`,
`y` of `X² - t X + a`, stated multiplied out so that it holds in any commutative ring and at a
repeated root; for the value at a repeated root itself use `dickson_two_eval_two_mul`. -/
theorem dickson_two_eval_add_mul_sub {x y a : R} (h : x * y = a) (n : ℕ) :
    (dickson 2 a n).eval (x + y) * (x - y) = x ^ (n + 1) - y ^ (n + 1) := by
  rw [dickson_two_eval_add h, ← geom_sum₂_mul]
  simp

/-- **At a repeated root the Dickson value is `(n + 1) * x ^ n`.**

These are the `t² = 4 a` terms of the Eichler–Selberg trace formula,
`P_k(± 2 √n, n) = (k - 1) * (± √n) ^ (k - 2)`, where `dickson_two_eval_add_mul_sub` degenerates to
`0 = 0`. -/
theorem dickson_two_eval_two_mul (x : R) (n : ℕ) :
    (dickson 2 (x ^ 2) n).eval (2 * x) = (n + 1) * x ^ n := by
  rw [sq, two_mul, dickson_two_eval_add rfl]
  simpa using geom_sum₂_self x (n + 1)

/-- **The Dickson polynomials of the second kind are homogeneous** of degree `n` when the parameter
is given weight two: scaling the argument by `s` and the parameter by `s ^ 2` scales the value by
`s ^ n`. -/
theorem dickson_two_eval_mul (s t a : R) (n : ℕ) :
    (dickson 2 (s ^ 2 * a) n).eval (s * t) = s ^ n * (dickson 2 a n).eval t := by
  induction n using Nat.twoStepInduction with
  | zero => simp [dickson_zero]
  | one => simp [dickson_one]
  | more n ih₀ ih₁ =>
    simp only [dickson_add_two, eval_sub, eval_mul, eval_X, eval_C, ih₀, ih₁]
    ring

/-- **The Dickson polynomial of the second kind with square parameter is a rescaled Chebyshev
polynomial**: `(dickson 2 (s ^ 2) n).eval (s * t) = s ^ n * (Chebyshev.S R n).eval t`.

Since `Chebyshev.S R n` is `U_n(X / 2)`, this is the division-free form of the identity
`P_k(t, s²) = s ^ (k - 2) * U_{k-2}(t / (2 s))` relating the Eichler–Selberg weights to the
Chebyshev polynomials of the second kind. -/
theorem dickson_two_sq_eval_mul (s t : R) (n : ℕ) :
    (dickson 2 (s ^ 2) n).eval (s * t) = s ^ n * (Chebyshev.S R n).eval t := by
  simpa [dickson_two_one_eq_chebyshev_S] using dickson_two_eval_mul s t 1 n

/-- **The generating function of the Dickson values**:
`(1 - t X + a X²) * ∑ₙ (dickson 2 a n).eval t * Xⁿ = 1` in `R⟦X⟧`.

This is the definition of the Eichler–Selberg weights `P_k(t, a)` by their generating function
`(1 - t x + a x²)⁻¹`, so it identifies them with the Dickson values `(dickson 2 a (k - 2)).eval t`
in any commutative ring, with no inverse taken. -/
theorem dickson_two_eval_mul_mk_eq_one (t a : R) :
    (1 - PowerSeries.C t * PowerSeries.X + PowerSeries.C a * PowerSeries.X ^ 2) *
      PowerSeries.mk (fun n ↦ (dickson 2 a n).eval t) = 1 := by
  rw [add_mul, sub_mul, one_mul, mul_assoc, mul_assoc]
  ext (_ | _ | n)
  · simp [dickson_zero]; norm_num
  · simp [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_X_pow_mul', dickson_one, dickson_zero]
    norm_num
  · simp [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_X_pow_mul', dickson_add_two]

end Polynomial
