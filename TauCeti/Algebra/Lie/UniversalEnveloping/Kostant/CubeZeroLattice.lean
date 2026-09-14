/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.CoordinateLattice
public import TauCeti.RingTheory.DividedPowers.Associative

/-!
# Admissibility of the coordinate lattice for cube-zero root operators

The coordinate `ℤ`-lattice of a standard representation is stable under the Kostant integral form
as soon as every designated root operator preserves it together with all of its divided powers.
When a root operator squares to zero only its first divided power can act, and
`TauCeti.UniversalEnvelopingAlgebra.kostantForm_apply_mem_coordinateLattice` records the
resulting criterion. This file supplies the next case: a root operator that cubes to zero, for
which the divided square `x² / 2` is the one further operator whose integrality has to be checked.
This is the situation of a simple root vector acting on a three-term weight string, such as a
short root vector of type `G₂` on the seven-dimensional module.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.kostantForm_apply_mem_coordinateLattice_of_pow_three_eq_zero`:
  the coordinate lattice is admissible for a Kostant form whose root operators cube to zero and
  preserve it together with their divided squares.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L] {κ : Type v} {ν : Type w}
variable {ι : Type*} [Finite ι] [DecidableEq ι]

/-- **The coordinate lattice of a standard representation is admissible for cube-zero root
operators.** The Kostant `ℤ`-form presented by root operators that cube to zero and preserve the
coordinate lattice together with their divided squares, and by Cartan operators with integral
coordinate weights, preserves the coordinate `ℤ`-lattice. -/
theorem kostantForm_apply_mem_coordinateLattice_of_pow_three_eq_zero (e : ν → L) (h : κ → L)
    (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ (ι → ℚ))
    {wt : ι → κ → ℤ}
    (hcube : ∀ k, ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k)) ^ 3 = 0)
    (hstab : ∀ k, ∀ v ∈ TauCeti.coordinateLattice ι,
      ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k)) v ∈ TauCeti.coordinateLattice ι)
    (hstab₂ : ∀ k, ∀ v ∈ TauCeti.coordinateLattice ι,
      Associative.dividedPower 2 (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))) v ∈
        TauCeti.coordinateLattice ι)
    (hwt : ∀ a, IsCartanWeightVector h ρ (wt a) (Pi.single a 1))
    {u : _root_.UniversalEnvelopingAlgebra ℚ L} (hu : u ∈ kostantForm e h)
    {v : ι → ℚ} (hv : v ∈ TauCeti.coordinateLattice ι) :
    ρ u v ∈ TauCeti.coordinateLattice ι :=
  kostantForm_apply_mem e h ρ (TauCeti.coordinateLattice ι)
    (fun k m _ hw => by
      rw [Associative.map_dividedPower]
      exact Associative.dividedPower_apply_mem_of_pow_three_eq_zero _
        (TauCeti.coordinateLattice ι).toAddSubgroup (hcube k)
        (fun hw' => hstab k _ hw') (fun hw' => hstab₂ k _ hw') m hw)
    (fun i m _ hw => ringChoose_apply_mem_coordinateLattice h ρ hwt i m hw) u hu hv

end TauCeti.UniversalEnvelopingAlgebra
