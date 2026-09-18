/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.BaseChange
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Cancelling iterated base change for Lie algebras

This file upgrades the linear equivalence
`TensorProduct.AlgebraTensorModule.cancelBaseChange` to a Lie algebra equivalence.
-/

public section

open scoped TensorProduct

namespace LieAlgebra.ExtendScalars

variable (R S A L : Type*) [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]
  [LieRing L] [LieAlgebra R L]

/-- Iterating extension of scalars from `R` through `S` to `A` gives the same Lie algebra as
extending scalars directly from `R` to `A`. -/
def cancelBaseChange : A ⊗[S] (S ⊗[R] L) ≃ₗ⁅A⁆ A ⊗[R] L := by
  let sourceLieRingModule : LieRingModule (A ⊗[S] (S ⊗[R] L)) (A ⊗[S] (S ⊗[R] L)) :=
    inferInstance
  let targetLieRingModule : LieRingModule (A ⊗[R] L) (A ⊗[R] L) := inferInstance
  letI : Bracket (A ⊗[S] (S ⊗[R] L)) (A ⊗[S] (S ⊗[R] L)) :=
    sourceLieRingModule.toBracket
  letI : Bracket (A ⊗[R] L) (A ⊗[R] L) := targetLieRingModule.toBracket
  let e := TensorProduct.AlgebraTensorModule.cancelBaseChange R S A A L
  exact
    { __ := e
      map_lie' := by
        intro x y
        change e ⁅x, y⁆ = ⁅e x, e y⁆
        induction x using TensorProduct.induction_on with
        | zero =>
          have hzero : ⁅(0 : A ⊗[S] (S ⊗[R] L)), y⁆ = 0 := zero_lie y
          rw [hzero, e.map_zero, zero_lie]
        | tmul a sx =>
          induction sx using TensorProduct.induction_on with
          | zero =>
            rw [TensorProduct.tmul_zero]
            have hzero : ⁅(0 : A ⊗[S] (S ⊗[R] L)), y⁆ = 0 := zero_lie y
            rw [hzero, e.map_zero, zero_lie]
          | tmul s x =>
            induction y using TensorProduct.induction_on with
            | zero => rw [lie_zero (L := A ⊗[S] (S ⊗[R] L)), e.map_zero, lie_zero]
            | tmul b ty =>
              induction ty using TensorProduct.induction_on with
              | zero => rw [TensorProduct.tmul_zero, lie_zero (L := A ⊗[S] (S ⊗[R] L)),
                  e.map_zero, lie_zero]
              | tmul t y =>
                simp only [bracket_tmul]
                rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
                  TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
                  TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, bracket_tmul]
                simp only [Algebra.smul_def, map_mul]
                rw [mul_mul_mul_comm]
              | add u v hu hv =>
                rw [TensorProduct.tmul_add, lie_add (L := A ⊗[S] (S ⊗[R] L)),
                  e.map_add, hu, hv, e.map_add, lie_add]
            | add u v hu hv =>
              rw [lie_add (L := A ⊗[S] (S ⊗[R] L)), e.map_add, hu, hv, e.map_add,
                lie_add]
          | add u v hu hv =>
            rw [TensorProduct.tmul_add]
            have hadd : ⁅a ⊗ₜ[S] u + a ⊗ₜ[S] v, y⁆ =
                ⁅a ⊗ₜ[S] u, y⁆ + ⁅a ⊗ₜ[S] v, y⁆ := add_lie _ _ _
            rw [hadd, e.map_add, hu, hv, e.map_add, add_lie]
        | add u v hu hv =>
          have hadd : ⁅u + v, y⁆ = ⁅u, y⁆ + ⁅v, y⁆ := add_lie _ _ _
          rw [hadd, e.map_add, hu, hv, e.map_add, add_lie] }

@[simp]
theorem cancelBaseChange_tmul (a : A) (s : S) (x : L) :
    cancelBaseChange R S A L (a ⊗ₜ[S] (s ⊗ₜ[R] x)) = (s • a) ⊗ₜ[R] x :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul R S A a x s

@[simp]
theorem cancelBaseChange_symm_tmul (a : A) (x : L) :
    (cancelBaseChange R S A L).symm (a ⊗ₜ[R] x) = a ⊗ₜ[S] (1 ⊗ₜ[R] x) :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul R S A a x

end LieAlgebra.ExtendScalars
