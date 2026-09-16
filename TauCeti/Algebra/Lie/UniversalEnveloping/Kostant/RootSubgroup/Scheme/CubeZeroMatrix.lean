/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ClosedImmersion

/-!
# The matrix of a cube-zero root subgroup

The matrix of a Kostant root subgroup at parameter `t` is the divided-power exponential
`∑ₖ tᵏ e⁽ᵏ⁾` of the root operator, read in the chosen lattice basis. When the operator squares to
zero this is `1 + t X` for the integral matrix `X` of the operator, which is
`TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix_eq_one_add_smul`. This file treats the
next case, an operator that cubes to zero, where one more term survives:

```text
xᵢ(t) = 1 + t X + t² Y,
```

`Y` being the integral matrix of the divided square `e⁽²⁾ = e² / 2` on the lattice. This is the
shape of a simple root subgroup acting through a three-term weight string, such as a short root
subgroup of type `G₂` on the seven-dimensional module. The equation is proved on every
algebra-valued point and then read on the coordinate morphism, where it lets a consumer check a
matrix equation on all points of the root subgroup at once.

## Main results

Both live in the namespace `TauCeti.UniversalEnvelopingAlgebra`.

* `kostantRootSubgroupMatrix_eq_one_add_smul_add_smul`: the matrix of a cube-zero root subgroup
  at a point is `1 + t X + t² Y`.
* `exists_map_genericMatrix_kostantRootSubgroupCoordinateMap_eq_one_add_smul_add_smul`: the same
  equation on the generic matrix, along the root-subgroup coordinate morphism.
-/

public section

open AlgebraicGeometry CategoryTheory TensorProduct WithConv

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

section GenericMatrix

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {ι : Type w} {κ : Type*}
variable {V : Type} [AddCommGroup V] [Module ℚ V]
variable (e : ι → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ v ∈ M, ρ u v ∈ M)
variable (i : ι)
variable (hnil : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
variable {N : ℕ} (bb : Module.Basis (Fin N) ℤ M)

include hnil in
/-- **The generic matrix of a cube-zero root subgroup is `1 + t X + t² Y`.** This is
`TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix_eq_one_add_smul_add_smul` read on
the coordinate morphism rather than on a point: the entries of the generic matrix of `GL N` are
carried to those of `1 + t X + t² Y` for the parameter `t` of the universal point of `𝔾ₐ`. -/
theorem exists_map_genericMatrix_kostantRootSubgroupCoordinateMap_eq_one_add_smul_add_smul
    (X Y : Matrix (Fin N) (Fin N) ℤ)
    (hclass : nilpotencyClass
      (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) ≤ 3)
    (haction : ∀ s, ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)) (bb s : V) =
      ∑ r, X r s • (bb r : V))
    (hsquare : ∀ s, Associative.dividedPower 2
      (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) (bb s : V) =
        ∑ r, Y r s • (bb r : V)) :
    ∃ t : AdditiveGroup.coordinateHopfAlgebra ℤ,
      (GeneralLinear.genericMatrix ℤ N).map
          (kostantRootSubgroupCoordinateMap e h ρ M hM i hnil bb).hom.toAlgHom =
        1 + t • X.map (Int.cast : ℤ → AdditiveGroup.coordinateHopfAlgebra ℤ) +
          t ^ 2 • Y.map (Int.cast : ℤ → AdditiveGroup.coordinateHopfAlgebra ℤ) := by
  obtain ⟨q, hq⟩ :=
    exists_map_genericMatrix_eq_kostantRootSubgroupMatrix e h ρ M hM i hnil bb
  exact ⟨Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv q),
    hq.trans (kostantRootSubgroupMatrix_eq_one_add_smul_add_smul e h ρ M hM i hnil bb X Y hclass
      haction hsquare q)⟩

end GenericMatrix

end TauCeti.UniversalEnvelopingAlgebra
