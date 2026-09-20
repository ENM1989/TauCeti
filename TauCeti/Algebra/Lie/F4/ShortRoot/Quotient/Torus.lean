/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Quotient.Basis
public import TauCeti.LinearAlgebra.Basis.DiagonalTorus.Basic

/-!
# Torus pinning for the modular F4 quotient

The special character-lattice map sends a torus point `s` to
`(s₃², s₂², s₁, s₀)`.  This file proves the corresponding character identity
and specializes it to the quotient basis: its long-root weight has the same
character as the associated short-root weight after applying the special torus
map.  The two Cartan coordinates have weight zero on both sides.

## References

* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS 80 (1968), §11.
* R. W. Carter, *Simple Groups of Lie Type*, §12.3.
-/

public section

namespace TauCeti.DynkinType

open scoped _root_.Matrix

noncomputable section

/-- The torus-point map contravariant to the F4 special character-lattice map. -/
def f4SpecialIsogenyTorusMap {A : Type*} [CommRing A]
    (s : Fin 4 → Aˣ) : Fin 4 → Aˣ :=
  ![s 3 ^ 2, s 2 ^ 2, s 1, s 0]

/-- Applying the special torus map twice is coordinatewise squaring. -/
@[simp] theorem f4SpecialIsogenyTorusMap_self
    {A : Type*} [CommRing A] (s : Fin 4 → Aˣ) :
    f4SpecialIsogenyTorusMap (f4SpecialIsogenyTorusMap s) =
      fun i => s i ^ 2 := by
  ext i
  fin_cases i <;> simp [f4SpecialIsogenyTorusMap]

/-- Evaluation after the special torus map is evaluation after applying the
special character-lattice matrix. -/
theorem torusCharacter_f4SpecialIsogenyTorusMap
    {A : Type*} [CommRing A] (s : Fin 4 → Aˣ) (μ : Fin 4 → ℤ) :
    TauCeti.torusCharacter (f4SpecialIsogenyTorusMap s) μ =
      TauCeti.torusCharacter s (f4SpecialIsogenyMatrix *ᵥ μ) := by
  rw [TauCeti.torusCharacter_def, TauCeti.torusCharacter_def,
    f4SpecialIsogenyMatrix_def]
  have hcomm (a b c d : Aˣ) : a * (b * (c * d)) = d * (c * (b * a)) := by
    calc
      a * (b * (c * d)) = (a * b) * (c * d) := (mul_assoc _ _ _).symm
      _ = (c * d) * (a * b) := mul_comm _ _
      _ = (d * c) * (b * a) := congrArg₂ (· * ·) (mul_comm _ _) (mul_comm _ _)
      _ = d * (c * (b * a)) := mul_assoc _ _ _
  simpa [f4SpecialIsogenyTorusMap, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, Fin.prod_univ_succ, zpow_mul] using
      hcomm ((s 3 ^ 2) ^ μ 0) ((s 2 ^ 2) ^ μ 1) (s 1 ^ μ 2) (s 0 ^ μ 3)

/-- The quotient-basis weight: the long root paired with a nonzero short-root
weight, and zero on the two Cartan coordinates. -/
def f4ShortRootQuotientWeight (a : Fin 26) : Fin 4 → ℤ :=
  match f4ShortRootWeightIndexEquiv a with
  | Sum.inl i => f4Root (f4SpecialIsogenyIndexEquiv i)
  | Sum.inr _ => 0

@[simp] theorem f4ShortRootQuotientWeight_symm_inl (i : F4ShortRootIndex) :
    f4ShortRootQuotientWeight (f4ShortRootWeightIndexEquiv.symm (Sum.inl i)) =
      f4Root (f4SpecialIsogenyIndexEquiv i) := by
  simp only [f4ShortRootQuotientWeight, Equiv.apply_symm_apply]

@[simp] theorem f4ShortRootQuotientWeight_symm_inr (j : Fin 2) :
    f4ShortRootQuotientWeight (f4ShortRootWeightIndexEquiv.symm (Sum.inr j)) = 0 := by
  simp only [f4ShortRootQuotientWeight, Equiv.apply_symm_apply]

/-- The quotient-basis character equals the target short-root character after
the special torus map. -/
theorem torusCharacter_f4ShortRootQuotientWeight
    {A : Type*} [CommRing A] (s : Fin 4 → Aˣ) (a : Fin 26) :
    TauCeti.torusCharacter s (f4ShortRootQuotientWeight a) =
      TauCeti.torusCharacter (f4SpecialIsogenyTorusMap s) (f4ShortRootWeight a) := by
  rcases h : f4ShortRootWeightIndexEquiv a with i | j
  · have ha : a = f4ShortRootWeightIndexEquiv.symm (Sum.inl i) := by
      apply f4ShortRootWeightIndexEquiv.injective
      rw [h, Equiv.apply_symm_apply]
    subst a
    rw [torusCharacter_f4SpecialIsogenyTorusMap]
    simp only [f4ShortRootQuotientWeight, Equiv.apply_symm_apply,
      f4ShortRootWeight_f4ShortRootWeightIndexEquiv_symm_inl]
    rw [← f4SimplyConnectedRootDatum_root,
      f4SpecialIsogenyMatrix_mulVec_root]
    simp only [i.property, one_smul]
  · have ha : a = f4ShortRootWeightIndexEquiv.symm (Sum.inr j) := by
      apply f4ShortRootWeightIndexEquiv.injective
      rw [h, Equiv.apply_symm_apply]
    subst a
    simp only [f4ShortRootQuotientWeight, Equiv.apply_symm_apply,
      f4ShortRootWeight_f4ShortRootWeightIndexEquiv_symm_inr, TauCeti.torusCharacter_zero]

/-- The quotient-basis character identity after coercing units to the scalar ring. -/
theorem coe_torusCharacter_f4ShortRootQuotientWeight
    {A : Type*} [CommRing A] (s : Fin 4 → Aˣ) (a : Fin 26) :
    ((TauCeti.torusCharacter s (f4ShortRootQuotientWeight a) : Aˣ) : A) =
      ((TauCeti.torusCharacter (f4SpecialIsogenyTorusMap s)
        (f4ShortRootWeight a) : Aˣ) : A) :=
  congrArg Units.val (torusCharacter_f4ShortRootQuotientWeight s a)

end

end TauCeti.DynkinType
