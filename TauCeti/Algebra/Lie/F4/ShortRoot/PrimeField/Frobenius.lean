/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.PointsFunctor
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Frobenius on the short-root type-F4 prime-field carrier

This file defines the Frobenius endomorphisms of the carrier's matrix-valued points. The
finite-field Frobenius algebra homomorphism exists for every `ZMod 2`-algebra, including the zero
ring, so the coefficient formula and all functor laws need no separate characteristic hypothesis.

## Main declarations

* `PrimeField.frobenius` is the point map induced by an iterate of the finite-field Frobenius.
* `PrimeField.coe_frobenius_apply` is its entrywise `2 ^ m`-power formula.
* `PrimeField.frobenius_zero` and `PrimeField.frobenius_add` are the iteration laws inherited from
  point functoriality.
* `PrimeField.frobenius_rootSubgroupPoints` and `PrimeField.frobenius_weightTorusPoints` describe
  the action on the pinned generators.
-/

public section

open scoped Matrix

namespace TauCeti.F4ShortRoot

universe v

namespace PrimeField

/-- **The `2 ^ m`-power Frobenius endomorphism of the carrier over `𝔽₂`**, the map on points
induced by the iterated Frobenius of the value algebra.

For `m` positive this is the `2 ^ m`-power Frobenius of the carrier's points; at `m = 0` it is the
identity. -/
noncomputable def frobenius (m : ℕ) (A : Type v) [CommRing A] [Algebra (ZMod 2) A] :
    points A →* points A := pointsMap ((FiniteField.frobeniusAlgHom (ZMod 2) A) ^ m)

/-- The `m`-th power of the finite-field Frobenius raises elements to their `2 ^ m`-th power. -/
private theorem frobeniusAlgHom_pow_apply (m : ℕ) (A : Type v) [CommRing A] [Algebra (ZMod 2) A]
    (x : A) : ((FiniteField.frobeniusAlgHom (ZMod 2) A) ^ m) x = x ^ 2 ^ m := by
  rw [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, ZMod.card]

/-- The Frobenius endomorphism of the carrier over `𝔽₂` maps matrices entrywise by the finite-field
Frobenius algebra homomorphism. -/
theorem coe_frobenius (m : ℕ) (A : Type v) [CommRing A] [Algebra (ZMod 2) A]
    (g : points A) :
    (frobenius m A g : _root_.Matrix.GeneralLinearGroup (Fin 26) A) =
      _root_.Matrix.GeneralLinearGroup.map
        (((FiniteField.frobeniusAlgHom (ZMod 2) A) ^ m : A →ₐ[ZMod 2] A) : A →+* A) g := by
  simpa only [frobenius] using
    coe_pointsMap ((FiniteField.frobeniusAlgHom (ZMod 2) A) ^ m) g

/-- Entrywise, the Frobenius endomorphism of the carrier over `𝔽₂` raises each matrix coefficient
to its `2 ^ m`-th power. -/
@[simp]
theorem coe_frobenius_apply (m : ℕ) (A : Type v) [CommRing A] [Algebra (ZMod 2) A]
    (g : points A) (i j : Fin 26) :
    ((frobenius m A g : _root_.Matrix.GeneralLinearGroup (Fin 26) A) :
        Matrix (Fin 26) (Fin 26) A) i j =
      ((g : _root_.Matrix.GeneralLinearGroup (Fin 26) A) :
        Matrix (Fin 26) (Fin 26) A) i j ^ 2 ^ m := by
  rw [coe_frobenius, _root_.Matrix.GeneralLinearGroup.map_apply]
  exact frobeniusAlgHom_pow_apply m A
    (((g : _root_.Matrix.GeneralLinearGroup (Fin 26) A) :
      Matrix (Fin 26) (Fin 26) A) i j)

/-- The zeroth Frobenius iterate is the identity on the carrier's point group. -/
@[simp]
theorem frobenius_zero (A : Type v) [CommRing A] [Algebra (ZMod 2) A] :
    frobenius 0 A = MonoidHom.id _ := by
  have h : (1 : A →ₐ[ZMod 2] A) = AlgHom.id (ZMod 2) A := by ext; rfl
  rw [frobenius, pow_zero, h, pointsMap_id]

/-- Frobenius iterates add under composition on the carrier's point group. -/
theorem frobenius_add (m k : ℕ) (A : Type v) [CommRing A] [Algebra (ZMod 2) A] :
    frobenius (m + k) A = (frobenius m A).comp (frobenius k A) := by
  let F := FiniteField.frobeniusAlgHom (ZMod 2) A
  have hcomp : F ^ m * F ^ k = (F ^ m).comp (F ^ k) := rfl
  rw [frobenius, frobenius, frobenius, pow_add, hcomp, pointsMap_comp]

/-- **Frobenius raises the parameter of every numbered simple root subgroup to its `2 ^ m`-th
power.** -/
@[simp]
theorem frobenius_rootSubgroupPoints (m : ℕ) (A : Type v) [CommRing A] [Algebra (ZMod 2) A]
    (k : Fin 4 ⊕ Fin 4) (u : Multiplicative A) :
    frobenius m A (rootSubgroupPoints k A u) =
      rootSubgroupPoints k A (Multiplicative.ofAdd (Multiplicative.toAdd u ^ 2 ^ m)) := by
  rw [frobenius, pointsMap_rootSubgroupPoints]
  congr 2
  exact frobeniusAlgHom_pow_apply m A (Multiplicative.toAdd u)

/-- **Frobenius raises every coordinate of the pinned split weight torus to its `2 ^ m`-th
power.** -/
@[simp]
theorem frobenius_weightTorusPoints (m : ℕ) (A : Type v) [CommRing A] [Algebra (ZMod 2) A]
    (s : Fin 4 → Aˣ) :
    frobenius m A (weightTorusPoints A s) = weightTorusPoints A (s ^ 2 ^ m) := by
  rw [frobenius, pointsMap_weightTorusPoints]
  congr 1
  funext i
  apply Units.ext
  exact frobeniusAlgHom_pow_apply m A (s i)

end PrimeField

end TauCeti.F4ShortRoot
