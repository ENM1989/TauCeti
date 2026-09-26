/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Cartier.Inverse

/-!
# Relative cohomology and symmetric powers of algebraic curves

This file formalizes the symmetric powers of a smooth algebraic curve over a field `k`,
advancing toward Layer C of the Jacobian challenge. The `d`-th symmetric power `Symᵈ(C)`
is modeled as the moduli of relative effective Cartier divisors of degree `d`, which
coincide with effective codimension-one Weil divisors via the Weil-Cartier equivalence
on regular curves.

<!--tauceti-target:v1
  {"focus":"JacobianChallenge",
   "id":"JacobianChallenge.Relative_cohomology_and_symmetric_powers"}-->
-/

public section

open CategoryTheory AlgebraicGeometry Order

namespace TauCeti.JacobianChallenge

universe u

/-- A geometric algebraic curve over a ground field `k`: an integral scheme of dimension
at most one whose codimension-one local rings are discrete valuation rings. -/
structure GeometricCurve (k : Type u) [Field k] where
  /-- The underlying scheme of the curve. -/
  Scheme : AlgebraicGeometry.Scheme.{u}
  /-- The scheme is integral. -/
  [isIntegral : AlgebraicGeometry.IsIntegral Scheme]
  /-- Codimension-one local rings are discrete valuation rings. -/
  [isDVR : ∀ y : AlgebraicGeometry.CodimensionOnePoint Scheme,
    IsDiscreteValuationRing (Scheme.presheaf.stalk (y : Scheme))]
  /-- The curve is a scheme over `Spec k`. -/
  [overSpec : Scheme.Over (AlgebraicGeometry.Spec (.of k))]
  /-- The curve has dimension at most one (coheight ≤ 1). -/
  dim_le_one : ∀ x : Scheme, coheight x ≤ 1

attribute [instance] GeometricCurve.isIntegral GeometricCurve.isDVR GeometricCurve.overSpec

variable {k : Type u} [Field k] (C : GeometricCurve k)

/-- The `d`-th symmetric power of an algebraic curve `C` over `k`, modeled as the moduli
of relative effective Cartier divisors of degree `d`: effective codimension-one cycles
whose relative degree over `k` equals `d`. -/
def SymmetricPower (d : ℕ) : Type _ :=
  { D : SchemeWeilDivisor C.Scheme //
    WeilDivisor.IsEffective D ∧
    SchemeWeilDivisor.relativeDegree (C.Scheme ↘ AlgebraicGeometry.Spec (.of k)) D = d }

/-- The unique relative effective Cartier divisor of degree zero (the empty divisor). -/
def symZero : SymmetricPower C 0 :=
  ⟨0, WeilDivisor.isEffective_zero, by simp [map_zero]⟩

/-- Monoidal addition map on symmetric powers: summing effective cycles adds degrees. -/
noncomputable def symAdd {d₁ d₂ : ℕ}
    (D₁ : SymmetricPower C d₁) (D₂ : SymmetricPower C d₂) : SymmetricPower C (d₁ + d₂) :=
  ⟨D₁.1 + D₂.1,
    WeilDivisor.isEffective_add D₁.2.1 D₂.2.1,
    by rw [map_add, D₁.2.2, D₂.2.2]⟩

/-- Identity law: adding the zero divisor yields the original effective divisor. -/
theorem symAdd_zero {d : ℕ} (D : SymmetricPower C d) :
    (symAdd C D (symZero C)).1 = D.1 := by
  change D.1 + 0 = D.1
  rw [add_zero]

/-- Associativity of addition on symmetric powers of an algebraic curve. -/
theorem symAdd_assoc {d₁ d₂ d₃ : ℕ}
    (D₁ : SymmetricPower C d₁) (D₂ : SymmetricPower C d₂) (D₃ : SymmetricPower C d₃) :
    (symAdd C D₁ (symAdd C D₂ D₃)).1 = (symAdd C (symAdd C D₁ D₂) D₃).1 := by
  change D₁.1 + (D₂.1 + D₃.1) = (D₁.1 + D₂.1) + D₃.1
  rw [add_assoc]

/-- The canonical embedding of symmetric powers into Cartier divisors on the curve. -/
noncomputable def toCartierDivisor {d : ℕ}
    (D : SymmetricPower C d) : AlgebraicGeometry.Scheme.CartierDivisor C.Scheme :=
  SchemeWeilDivisor.equivCartierDivisor C.dim_le_one D.1

end TauCeti.JacobianChallenge
