/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.RiemannRoch.Basic

/-!
# Riemann-Roch and Serre duality for algebraic curves

This file formalizes the Riemann-Roch theorem for Weil divisors on a proper integral
curve over a field `k` with a `k`-rational point, building on Tau Ceti's scheme-theoretic
divisor cohomology library.

<!--tauceti-target:v1
  {"focus":"JacobianChallenge",
   "id":"JacobianChallenge.Riemann_Roch_and_Serre_duality"}-->
-/

public section

open CategoryTheory AlgebraicGeometry Order
open Module (finrank)

namespace TauCeti.JacobianChallenge

universe u

variable {X : Scheme.{u}} [IsIntegral X]
  [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]
  (k : Type u) [Field k] [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
  [FiniteDimensional k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1)]
  (hX : ∀ y : X, coheight y ≤ 1) {s : Spec (.of k) ⟶ X}
  (hs : s ≫ X ↘ Spec (.of k) = 𝟙 (Spec (.of k)))

/-- The Riemann-Roch theorem for a Weil divisor on an algebraic curve:
`dim H⁰(X, 𝒪_X(D)) - dim H¹(X, 𝒪_X(D)) = deg D + 1 - g`. -/
theorem riemann_roch (D : SchemeWeilDivisor X) :
    letI : IsLocallyNoetherian X :=
      LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
    (finrank k (Scheme.Modules.Cohomology (SchemeWeilDivisor.sheaf D) 0) : ℤ) -
        (finrank k (Scheme.Modules.Cohomology (SchemeWeilDivisor.sheaf D) 1) : ℤ) =
      SchemeWeilDivisor.relativeDegree (X ↘ Spec (.of k)) D + 1 - X.genus k :=
  SchemeWeilDivisor.finrank_cohomology_zero_sheaf_sub_finrank_cohomology_one_sheaf
    k hX hs D

/-- Riemann's inequality on an algebraic curve:
`dim H⁰(X, 𝒪_X(D)) ≥ deg D + 1 - g`. -/
theorem riemann_inequality (D : SchemeWeilDivisor X) :
    SchemeWeilDivisor.relativeDegree (X ↘ Spec (.of k)) D + 1 - X.genus k ≤
      finrank k (Scheme.Modules.Cohomology (SchemeWeilDivisor.sheaf D) 0) :=
  SchemeWeilDivisor.relativeDegree_add_one_sub_genus_le_finrank_cohomology_zero_sheaf
    k hX hs D

end TauCeti.JacobianChallenge
