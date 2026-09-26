/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.RealProjective.Basic
public import TauCeti.Topology.Homotopy.HomotopyGroup.Covering

/-!
# Higher homotopy of real projective space and spheres

This file formalizes the higher homotopy group isomorphism between real projective
space `RPⁿ` and its two-fold covering unit sphere `Sⁿ`. Because the antipodal projection
`mk : Sⁿ → RPⁿ` is a covering map, postcomposition with `mk` induces a canonical group
isomorphism `π_k(Sⁿ, x) ≃* π_k(RPⁿ, [x])` for every `k ≥ 2` (modeled by any nontrivial
index type `N`).

<!--tauceti-target:v1
  {"focus":"UniversalCovers",
   "id":"UniversalCovers.Higher_homotopy_of__RP___and_of_spheres"}-->
-/

public section

namespace UniversalCovers

open Metric
open TauCeti
open TauCeti.RealProjectiveSpace

variable (n : ℕ) {N : Type*} [Nontrivial N]
variable (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)

/-- The higher homotopy group isomorphism `π_N(Sⁿ, x) ≃* π_N(RPⁿ, [x])` for `N` with at least
two elements (i.e. dimension ≥ 2), induced by the antipodal covering projection. -/
noncomputable def realProjectiveSphereHomotopyGroupMulEquiv :
    HomotopyGroup N (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) x ≃*
      HomotopyGroup N (RealProjectiveSpace n) (RealProjectiveSpace.mk n x) :=
  (RealProjectiveSpace.isCoveringMap_mk n).homotopyGroupMulEquiv x

/-- Higher homotopy groups of real projective space and spheres coincide for all `k ≥ 2`. -/
theorem higher_homotopy_of_rp_and_spheres :
    Nonempty (HomotopyGroup N (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) x ≃*
      HomotopyGroup N (RealProjectiveSpace n) (RealProjectiveSpace.mk n x)) :=
  ⟨realProjectiveSphereHomotopyGroupMulEquiv n x⟩

end UniversalCovers
