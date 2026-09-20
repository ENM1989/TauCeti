/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Modular.Basis

/-!
# The adjoint action on the modular F4 short-root ideal

This file restricts the adjoint action of the reduced Chevalley Lie algebra to its modular
short-root ideal and expresses that action in the canonical twenty-six-coordinate basis.

## References

* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS 80 (1968), §11.
* R. W. Carter, *Simple Groups of Lie Type*, §12.3.
-/

public section

namespace TauCeti.DynkinType

open _root_.LieAlgebra LieModule

noncomputable section

/-- The coordinate basis of the modular short-root Lie ideal. -/
noncomputable def f4ShortRootLieIdealBasis :
    Module.Basis (Fin 26) (ZMod 2) f4ShortRootLieIdeal :=
  f4ShortRootBasis.map
    (LinearEquiv.ofEq _ _ f4ShortRootLieIdeal_toSubmodule.symm)

@[simp] theorem coe_f4ShortRootLieIdealBasis (a : Fin 26) :
    (f4ShortRootLieIdealBasis a : f4ModularChevalleyLieAlgebra) =
      f4ModularChevalleyBasis (f4ShortRootBasisCoordinate a) := by
  exact (LinearEquiv.coe_ofEq_apply f4ShortRootLieIdeal_toSubmodule.symm
    (f4ShortRootBasis a)).trans (coe_f4ShortRootBasis a)

theorem coe_f4ShortRootLieIdealBasis_symm_inl (i : F4ShortRootIndex) :
    (f4ShortRootLieIdealBasis (f4ShortRootWeightIndexEquiv.symm (Sum.inl i)) :
      f4ModularChevalleyLieAlgebra) = f4ModularRootVector i := by
  rw [coe_f4ShortRootLieIdealBasis, ← coe_f4ShortRootBasis]
  exact coe_f4ShortRootBasis_symm_inl i

/-- An ideal basis vector of root weight is the corresponding ambient root vector. -/
theorem coe_f4ShortRootLieIdealBasis_of_weight_eq_root (b : Fin 26) (i : Fin 48)
    (hi : f4Length i = 1) (h : f4ShortRootWeight b = f4Root i) :
    (f4ShortRootLieIdealBasis b : f4ModularChevalleyLieAlgebra) =
      f4ModularRootVector i := by
  have hb : b = f4ShortRootWeightIndexEquiv.symm (Sum.inl ⟨i, hi⟩) := by
    apply f4ShortRootWeightIndexEquiv.injective
    rw [Equiv.apply_symm_apply]
    exact (f4ShortRootWeightIndexEquiv_apply_eq_inl_iff _ _).2 h
  calc
    _ = (f4ShortRootLieIdealBasis
        (f4ShortRootWeightIndexEquiv.symm (Sum.inl ⟨i, hi⟩)) :
          f4ModularChevalleyLieAlgebra) := congrArg
            (fun j => (f4ShortRootLieIdealBasis j :
              f4ModularChevalleyLieAlgebra)) hb
    _ = _ := coe_f4ShortRootLieIdealBasis_symm_inl ⟨i, hi⟩

theorem coe_f4ShortRootLieIdealBasis_twelve :
    (f4ShortRootLieIdealBasis 12 : f4ModularChevalleyLieAlgebra) =
      f4ModularSimpleCoroot (Fin.cast rank_F4.symm (2 : Fin 4)) := by
  rw [coe_f4ShortRootLieIdealBasis, ← coe_f4ShortRootBasis]
  exact coe_f4ShortRootBasis_twelve

theorem coe_f4ShortRootLieIdealBasis_thirteen :
    (f4ShortRootLieIdealBasis 13 : f4ModularChevalleyLieAlgebra) =
      f4ModularSimpleCoroot (Fin.cast rank_F4.symm (3 : Fin 4)) := by
  rw [coe_f4ShortRootLieIdealBasis, ← coe_f4ShortRootBasis]
  exact coe_f4ShortRootBasis_thirteen

/-- The adjoint action of the reduced Chevalley Lie algebra on its modular short-root ideal. -/
noncomputable def f4ShortRootAdjoint :=
  LieModule.toEnd (ZMod 2) f4ModularChevalleyLieAlgebra f4ShortRootLieIdeal

@[simp] theorem coe_f4ShortRootAdjoint_apply
    (x : f4ModularChevalleyLieAlgebra) (y : f4ShortRootLieIdeal) :
    (f4ShortRootAdjoint x y : f4ModularChevalleyLieAlgebra) =
      ⁅x, (y : f4ModularChevalleyLieAlgebra)⁆ := by
  rfl

/-- Coordinates in the ideal basis agree with the corresponding ambient Chevalley coordinates. -/
theorem f4ShortRootLieIdealBasis_repr (y : f4ShortRootLieIdeal) (i : Fin 26) :
    f4ShortRootLieIdealBasis.repr y i =
      f4ModularChevalleyBasis.repr (y : f4ModularChevalleyLieAlgebra)
        (f4ShortRootBasisCoordinate i) := by
  classical
  let f : f4ShortRootLieIdeal →ₗ[ZMod 2] ZMod 2 :=
    (Finsupp.lapply i).comp f4ShortRootLieIdealBasis.repr.toLinearMap
  let g : f4ShortRootLieIdeal →ₗ[ZMod 2] ZMod 2 :=
    (Finsupp.lapply (f4ShortRootBasisCoordinate i)).comp
      (f4ModularChevalleyBasis.repr.toLinearMap.comp
        f4ShortRootLieIdeal.toSubmodule.subtype)
  -- Both sides are evaluations of the indicated coordinate linear maps.
  change f y = g y
  apply LinearMap.congr_fun (f4ShortRootLieIdealBasis.ext fun j => ?_) y
  simp only [f, g, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    Finsupp.lapply_apply, Module.Basis.repr_self, Finsupp.single_apply]
  -- The submodule inclusion and the Lie-ideal coercion are the same underlying map.
  rw [show f4ShortRootLieIdeal.toSubmodule.subtype (f4ShortRootLieIdealBasis j) =
      (f4ShortRootLieIdealBasis j : f4ModularChevalleyLieAlgebra) by rfl,
    coe_f4ShortRootLieIdealBasis, f4ModularChevalleyBasis.repr_self,
    Finsupp.single_apply]
  by_cases hji : j = i
  · simp [hji]
  · have hcoord : f4ShortRootBasisCoordinate j ≠ f4ShortRootBasisCoordinate i :=
      fun h => hji (f4ShortRootBasisCoordinate_injective h)
    simp [hji, hcoord]

/-- Matrix of the modular short-root adjoint action in its integral-weight basis. -/
noncomputable abbrev f4ShortRootAdjointMatrix
    (X : f4ModularChevalleyLieAlgebra) : Matrix (Fin 26) (Fin 26) (ZMod 2) :=
  LinearMap.toMatrix f4ShortRootLieIdealBasis f4ShortRootLieIdealBasis
    (f4ShortRootAdjoint X)

/-- Each entry is the ambient Chevalley coordinate of the adjoint image of its ideal basis column.
-/
theorem f4ShortRootAdjointMatrix_apply
    (X : f4ModularChevalleyLieAlgebra) (i j : Fin 26) :
    f4ShortRootAdjointMatrix X i j =
      f4ModularChevalleyBasis.repr
        ⁅X, (f4ShortRootLieIdealBasis j : f4ModularChevalleyLieAlgebra)⁆
        (f4ShortRootBasisCoordinate i) := by
  calc
    _ = f4ShortRootLieIdealBasis.repr
        (f4ShortRootAdjoint X (f4ShortRootLieIdealBasis j)) i :=
      LinearMap.toMatrix_apply _ _ _ _ _
    _ = f4ModularChevalleyBasis.repr
        (f4ShortRootAdjoint X (f4ShortRootLieIdealBasis j) :
          f4ModularChevalleyLieAlgebra)
        (f4ShortRootBasisCoordinate i) :=
      f4ShortRootLieIdealBasis_repr _ _
    _ = _ := congrArg
      (fun Y : f4ModularChevalleyLieAlgebra =>
        f4ModularChevalleyBasis.repr Y (f4ShortRootBasisCoordinate i))
      (coe_f4ShortRootAdjoint_apply X (f4ShortRootLieIdealBasis j))

/-- The pinned root index of a positive or negative simple root. -/
def f4SignedSimpleRootIndex : Fin 4 ⊕ Fin 4 → Fin 48
  | .inl i => Fin.castAdd 44 i
  | .inr i => f4OppositeRootIndex (Fin.castAdd 44 i)

@[simp] theorem f4SignedSimpleRootIndex_inl (i : Fin 4) :
    f4SignedSimpleRootIndex (.inl i) = Fin.castAdd 44 i := by rfl

@[simp] theorem f4SignedSimpleRootIndex_inr (i : Fin 4) :
    f4SignedSimpleRootIndex (.inr i) = f4OppositeRootIndex (Fin.castAdd 44 i) := by rfl

/-- A pinned positive or negative simple root vector in the reduced Chevalley lattice. -/
noncomputable def f4ModularSignedSimpleRootVector (k : Fin 4 ⊕ Fin 4) :
    f4ModularChevalleyLieAlgebra :=
  f4ModularRootVector (f4SignedSimpleRootIndex k)

/-- The simple-root adjoint operator restricted to the modular short-root ideal. -/
noncomputable def f4ShortRootSimpleAdjoint (k : Fin 4 ⊕ Fin 4) :
    Module.End (ZMod 2) f4ShortRootLieIdeal :=
  f4ShortRootAdjoint (f4ModularSignedSimpleRootVector k)

@[simp] theorem coe_f4ShortRootSimpleAdjoint_apply
    (k : Fin 4 ⊕ Fin 4) (y : f4ShortRootLieIdeal) :
    (f4ShortRootSimpleAdjoint k y : f4ModularChevalleyLieAlgebra) =
      ⁅f4ModularRootVector (f4SignedSimpleRootIndex k), (y : f4ModularChevalleyLieAlgebra)⁆ := by
  rfl

/-- The matrix of the simple-root adjoint operator in the canonical short-root basis. -/
noncomputable def f4ShortRootSimpleAdjointMatrix (k : Fin 4 ⊕ Fin 4) :
    Matrix (Fin 26) (Fin 26) (ZMod 2) :=
  LinearMap.toMatrix f4ShortRootLieIdealBasis f4ShortRootLieIdealBasis
    (f4ShortRootSimpleAdjoint k)

/-- The simple-root matrix entry is the indicated ideal-basis coordinate of the column action. -/
@[simp] theorem f4ShortRootSimpleAdjointMatrix_apply
    (k : Fin 4 ⊕ Fin 4) (a b : Fin 26) :
    f4ShortRootSimpleAdjointMatrix k a b =
      (f4ShortRootLieIdealBasis.repr
        (f4ShortRootSimpleAdjoint k (f4ShortRootLieIdealBasis b))) a := by
  -- Unfold the named adjoint matrix to apply the general matrix-entry formula.
  change (LinearMap.toMatrix f4ShortRootLieIdealBasis f4ShortRootLieIdealBasis
    (f4ShortRootSimpleAdjoint k)) a b = _
  exact LinearMap.toMatrix_apply _ _ _ _ _

/-- On a short-root basis column whose translate is again short, the restricted adjoint action
is the translated short-root basis vector with coefficient one. -/
theorem f4ShortRootAdjoint_root_edge (α β γ : Fin 48)
    (hβ : f4Length β = 1) (hγ : f4Length γ = 1)
    (h : f4SimplyConnectedRootDatum.root γ =
      f4SimplyConnectedRootDatum.root β + f4SimplyConnectedRootDatum.root α) :
    f4ShortRootAdjoint (f4ModularRootVector α)
        (f4ShortRootLieIdealBasis
          (f4ShortRootWeightIndexEquiv.symm (Sum.inl ⟨β, hβ⟩))) =
      f4ShortRootLieIdealBasis
        (f4ShortRootWeightIndexEquiv.symm (Sum.inl ⟨γ, hγ⟩)) := by
  apply Subtype.ext
  simp only [coe_f4ShortRootAdjoint_apply, coe_f4ShortRootLieIdealBasis_symm_inl]
  exact f4Modular_lie_rootVector_of_add_eq_short α β γ hβ hγ h

/-- On the root coordinate opposite a short root, the restricted adjoint action lands in the
corresponding modular coroot. -/
theorem coe_f4ShortRootAdjoint_opposite (α : Fin 48)
    (hopp : f4Length (f4OppositeRootIndex α) = 1) :
    (f4ShortRootAdjoint (f4ModularRootVector α)
        (f4ShortRootLieIdealBasis
          (f4ShortRootWeightIndexEquiv.symm
            (Sum.inl ⟨f4OppositeRootIndex α, hopp⟩))) :
      f4ModularChevalleyLieAlgebra) = f4ModularCoroot α := by
  rw [coe_f4ShortRootAdjoint_apply, coe_f4ShortRootLieIdealBasis_symm_inl]
  exact f4Modular_lie_rootVector_opposite α

/-- On either short simple-coroot coordinate, the restricted adjoint action is the root vector
scaled by the reduced Cartan integer (with the bracket-order sign). -/
theorem coe_f4ShortRootAdjoint_simpleCoroot (α : Fin 48) (i : Fin F4.rank)
    (hi : Fin.cast rank_F4 i = 2 ∨ Fin.cast rank_F4 i = 3) :
    (f4ShortRootAdjoint (f4ModularRootVector α)
        ⟨f4ModularSimpleCoroot i,
          (mem_f4ShortRootLieIdeal_iff).mpr
            (f4ModularSimpleCoroot_mem_shortRootSubspace i hi)⟩ :
      f4ModularChevalleyLieAlgebra) =
      -(f4SimplyConnectedRootDatum.pairing α
        (Fin.castAdd 44 (Fin.cast rank_F4 i)) : ZMod 2) • f4ModularRootVector α := by
  -- The adjoint endomorphism is the ambient bracket, restricted to the ideal.
  change ⁅f4ModularRootVector α, f4ModularSimpleCoroot i⁆ = _
  rw [← lie_skew, f4Modular_lie_simpleCoroot_rootVector, neg_smul]

end

end TauCeti.DynkinType
