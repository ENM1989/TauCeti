/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Roadmap: JacobianChallenge
Target: The Picard scheme and Abel-Jacobi map
<!--tauceti-target:v1
  {"focus":"JacobianChallenge","id":"JacobianChallenge.The_Picard_scheme_and_Abel_Jacobi_map"}-->
-/

public section

namespace JacobianChallenge

noncomputable section

open Finsupp

/-- The group of Weil divisors on a curve with points `Points`,
modelled as formal finite sums of points with integer coefficients. -/
abbrev DivisorGroup (Points : Type*) := Points →₀ ℤ

/-- The single point divisor `[x]`. -/
def pointDivisor {Points : Type*} (x : Points) : DivisorGroup Points :=
  single x 1

/-- The degree map on divisors, sending `D = ∑ n_x [x]` to `∑ n_x`. -/
noncomputable def degreeHom {Points : Type*} : DivisorGroup Points →+ ℤ :=
  liftAddHom (fun _ => AddMonoidHom.id ℤ)

/-- Evaluating the degree on a single point divisor gives 1. -/
@[simp]
lemma degreeHom_pointDivisor {Points : Type*} (x : Points) :
    degreeHom (pointDivisor x) = 1 :=
  liftAddHom_apply_single (fun _ => AddMonoidHom.id ℤ) x 1

/-- The subgroup of degree-zero divisors `Div⁰(X) = ker deg`. -/
def degreeZeroDivisors (Points : Type*) : AddSubgroup (DivisorGroup Points) :=
  degreeHom.ker

/-- For any two points `x` and `x₀`, the divisor `[x] - [x₀]` has degree zero. -/
theorem pointDifference_mem_degreeZero {Points : Type*} (x x₀ : Points) :
    pointDivisor x - pointDivisor x₀ ∈ degreeZeroDivisors Points := by
  rw [degreeZeroDivisors, AddMonoidHom.mem_ker, map_sub,
      degreeHom_pointDivisor, degreeHom_pointDivisor, sub_self]

/-- The degree-corrected Abel-Jacobi divisor `[x] - [x₀]` of a point. -/
def abelJacobiDivisor {Points : Type*} (x₀ : Points) (x : Points) :
    degreeZeroDivisors Points :=
  ⟨pointDivisor x - pointDivisor x₀, pointDifference_mem_degreeZero x x₀⟩

/-- The Abel-Jacobi divisor of the basepoint is zero: `[x₀ - x₀] = 0`. -/
@[simp]
theorem abelJacobiDivisor_basepoint {Points : Type*} (x₀ : Points) :
    abelJacobiDivisor x₀ x₀ = 0 := by
  apply Subtype.ext
  simp only [abelJacobiDivisor, sub_self, ZeroMemClass.coe_zero]

/-- Data for the Jacobian variety `Pic⁰(X)` and Abel-Jacobi map on a curve with points `Points`
and chosen basepoint `x₀`. -/
structure AbelJacobiStructure (Points : Type*) (x₀ : Points) where
  /-- The subgroup of principal divisors of degree zero. -/
  principalDegreeZero : AddSubgroup (degreeZeroDivisors Points)

namespace AbelJacobiStructure

/-- The Jacobian variety / `Pic⁰(X)` as degree-zero divisors modulo principal divisors. -/
abbrev Jacobian {Points : Type*} {x₀ : Points} (S : AbelJacobiStructure Points x₀) : Type _ :=
  degreeZeroDivisors Points ⧸ S.principalDegreeZero

/-- The Abel-Jacobi map from the curve to its Jacobian variety `Pic⁰(X)`,
sending each point `x` to the divisor class of `[x] - [x₀]`. -/
def abelJacobi {Points : Type*} {x₀ : Points} (S : AbelJacobiStructure Points x₀)
    (x : Points) : S.Jacobian :=
  QuotientAddGroup.mk (abelJacobiDivisor x₀ x)

/-- The Abel-Jacobi map sends the chosen basepoint of the curve to the origin of the
Jacobian variety: `aj(x₀) = 0`. This is proven from the construction `[x₀ - x₀] = [0] = 0`. -/
@[simp]
theorem abel_jacobi_basepoint {Points : Type*} {x₀ : Points}
    (S : AbelJacobiStructure Points x₀) : S.abelJacobi x₀ = 0 := by
  rw [abelJacobi, abelJacobiDivisor_basepoint]
  rfl

end AbelJacobiStructure

end

end JacobianChallenge
