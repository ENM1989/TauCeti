/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal

/-!
# Matrices with at most one nonzero entry in each column

A *step matrix* is a square matrix each of whose columns is a scalar multiple of a coordinate
vector: the `b`th column is `c b` times the `t b`th coordinate vector, for a target function
`t` and a coefficient function `c`. Permutation matrices, diagonal matrices and the matrix
units are step matrices, and so is the matrix of any linear map that carries each vector of a
basis to a multiple of another vector of that basis, a situation common in explicit
representation theory.

This file records the property as `Matrix.IsStep` and the closure properties that make it
useful for computation: a product of step matrices is the step matrix of the composed targets
and the coefficients multiplied along the way, and entrywise application of a ring morphism
preserves the property. Since each entry of such a product is a single product of table lookups
rather than a sum over an index type, identities between explicitly tabulated step matrices
reduce to finitely many entrywise identities that need no summation.

The target of a column with coefficient zero is unconstrained, so the pair `(t, c)` is not
determined by the matrix; every statement below takes the witnessing pair as data.

## Main definitions

* `Matrix.IsStep`: the property, witnessed by a target function and a coefficient function.

## Main results

* `Matrix.IsStep.mul`: a product of step matrices is a step matrix.
* `Matrix.isStep_one`, `Matrix.isStep_diagonal`: the identity and the diagonal matrices.
* `Matrix.IsStep.map`: entrywise application of a ring morphism.
-/

public section

namespace Matrix

variable {n R S : Type*} [DecidableEq n]

/-- A matrix is a *step matrix* for a target function `t` and a coefficient function `c` when
its `b`th column is `c b` times the `t b`th coordinate vector. -/
@[expose] def IsStep [Zero R] (M : Matrix n n R) (t : n → n) (c : n → R) : Prop :=
  ∀ a b, M a b = if a = t b then c b else 0

section Zero

variable [Zero R] {M : Matrix n n R} {t : n → n} {c : n → R}

/-- The entry of a step matrix at a row other than the target of its column is zero. -/
theorem IsStep.apply_of_ne (h : M.IsStep t c) {a b : n} (hab : a ≠ t b) : M a b = 0 := by
  rw [h a b]
  exact ite_eq_right_iff.mpr fun hc => absurd hc hab

/-- The entry of a step matrix at the target of its column is the coefficient of that column. -/
theorem IsStep.apply_target (h : M.IsStep t c) (b : n) : M (t b) b = c b := by
  rw [h (t b) b]
  simp

end Zero

/-- A diagonal matrix is the step matrix of the identity target and its own diagonal. -/
theorem isStep_diagonal [Zero R] (d : n → R) : (diagonal d).IsStep id d := by
  intro a b
  change diagonal d a b = if a = b then d b else 0
  rw [diagonal_apply]
  split_ifs with h
  · rw [h]
  · rfl

/-- The identity matrix is the step matrix of the identity target and the constant coefficient
one. -/
theorem isStep_one [Zero R] [One R] : (1 : Matrix n n R).IsStep id 1 :=
  fun _ _ => one_apply

/-- **A product of step matrices is a step matrix**, with the composite target function and with
each coefficient the product of the two coefficients met along the way. -/
theorem IsStep.mul [Fintype n] [NonUnitalNonAssocSemiring R] {M N : Matrix n n R}
    {t t' : n → n} {c c' : n → R} (hM : M.IsStep t c) (hN : N.IsStep t' c') :
    (M * N).IsStep (t ∘ t') fun b => c (t' b) * c' b := by
  intro a b
  rw [mul_apply, Finset.sum_eq_single (t' b)]
  · rw [hM a (t' b), hN.apply_target b, Function.comp_apply]
    split_ifs
    · rfl
    · rw [zero_mul]
  · intro l _ hl
    rw [hN.apply_of_ne hl, mul_zero]
  · intro hb
    exact absurd (Finset.mem_univ (t' b)) hb

/-- Entrywise application of a ring morphism to a step matrix gives the step matrix of the same
target and the transformed coefficients. -/
theorem IsStep.map [NonAssocSemiring R] [NonAssocSemiring S] {M : Matrix n n R} {t : n → n}
    {c : n → R} (h : M.IsStep t c) (f : R →+* S) :
    (M.map f).IsStep t fun b => f (c b) := by
  intro a b
  rw [map_apply, h a b]
  split_ifs
  · rfl
  · exact map_zero f

end Matrix
