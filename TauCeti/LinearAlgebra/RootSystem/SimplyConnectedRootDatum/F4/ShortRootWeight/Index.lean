/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.F4.ShortRootWeight.Basic

/-!
# Indexing the short-root representation of type F4

The twenty-six coordinates of the short-root representation consist of the twenty-four short-root
weight spaces and two zero-weight coordinates. This file identifies their index type with the sum
of the short-root indices in the explicit type-`F₄` root table and `Fin 2`.

## Main declaration

* `TauCeti.DynkinType.f4ShortRootWeightIndexEquiv`: the equivalence between `Fin 26` and the
  twenty-four short-root labels together with two zero-weight labels.
-/

public section
namespace TauCeti.DynkinType

/-- The indices of the short roots in the explicit type-`F₄` root table. -/
abbrev F4ShortRootIndex := {i : Fin 48 // f4Length i = 1}

private theorem f4Root_ne_zero (i : Fin 48) : f4Root i ≠ 0 := by
  simpa using f4SimplyConnectedRootDatum.ne_zero i

private noncomputable def rootIndexOfNonzeroWeight (a : Fin 26)
    (ha : f4ShortRootWeight a ≠ 0) : F4ShortRootIndex :=
  ⟨Classical.choose ((f4ShortRootWeight_ne_zero_iff_exists_shortRoot a).mp ha),
    (Classical.choose_spec ((f4ShortRootWeight_ne_zero_iff_exists_shortRoot a).mp ha)).1⟩

@[simp] private theorem f4Root_rootIndexOfNonzeroWeight (a : Fin 26)
    (ha : f4ShortRootWeight a ≠ 0) :
    f4Root (rootIndexOfNonzeroWeight a ha) = f4ShortRootWeight a :=
  (Classical.choose_spec ((f4ShortRootWeight_ne_zero_iff_exists_shortRoot a).mp ha)).2

private noncomputable def weightIndexOfShortRoot (i : F4ShortRootIndex) : Fin 26 :=
  Classical.choose (exists_f4ShortRootWeight_eq_of_f4Length_eq_one i.property)

@[simp] private theorem f4ShortRootWeight_weightIndexOfShortRoot (i : F4ShortRootIndex) :
    f4ShortRootWeight (weightIndexOfShortRoot i) = f4Root i :=
  Classical.choose_spec (exists_f4ShortRootWeight_eq_of_f4Length_eq_one i.property)

private noncomputable def f4ShortRootSumIndex (a : Fin 26) : F4ShortRootIndex ⊕ Fin 2 :=
  if ha : f4ShortRootWeight a = 0 then
    Sum.inr (if a = 12 then 0 else 1)
  else
    Sum.inl (rootIndexOfNonzeroWeight a ha)

private noncomputable def f4ShortRootSumIndexInv : F4ShortRootIndex ⊕ Fin 2 → Fin 26
  | Sum.inl i => weightIndexOfShortRoot i
  | Sum.inr k => if k = 0 then 12 else 13

private theorem f4ShortRootSumIndexInv_apply_f4ShortRootSumIndex (a : Fin 26) :
    f4ShortRootSumIndexInv (f4ShortRootSumIndex a) = a := by
  by_cases ha : f4ShortRootWeight a = 0
  · rw [f4ShortRootWeight_eq_zero_iff] at ha
    rcases ha with rfl | rfl
    · have h12 : f4ShortRootWeight 12 = 0 :=
        (f4ShortRootWeight_eq_zero_iff 12).mpr (Or.inl rfl)
      simp [f4ShortRootSumIndex, f4ShortRootSumIndexInv, h12]
    · have h13 : f4ShortRootWeight 13 = 0 :=
        (f4ShortRootWeight_eq_zero_iff 13).mpr (Or.inr rfl)
      simp [f4ShortRootSumIndex, f4ShortRootSumIndexInv, h13]
  · simp only [f4ShortRootSumIndex, ha, ↓reduceDIte, f4ShortRootSumIndexInv]
    apply f4ShortRootWeight_injOn
    · change f4ShortRootWeight (weightIndexOfShortRoot (rootIndexOfNonzeroWeight a ha)) ≠ 0
      rw [f4ShortRootWeight_weightIndexOfShortRoot]
      exact f4Root_ne_zero (rootIndexOfNonzeroWeight a ha)
    · exact ha
    · simp

private theorem f4ShortRootSumIndex_apply_f4ShortRootSumIndexInv
    (x : F4ShortRootIndex ⊕ Fin 2) :
    f4ShortRootSumIndex (f4ShortRootSumIndexInv x) = x := by
  rcases x with i | k
  · have hne : f4ShortRootWeight (weightIndexOfShortRoot i) ≠ 0 := by
      simpa only [f4ShortRootWeight_weightIndexOfShortRoot] using f4Root_ne_zero i
    simp only [f4ShortRootSumIndexInv, f4ShortRootSumIndex, hne, ↓reduceDIte,
      Sum.inl.injEq]
    apply Subtype.ext
    apply f4Root.injective
    simp
  · fin_cases k
    · have h12 : f4ShortRootWeight 12 = 0 :=
        (f4ShortRootWeight_eq_zero_iff 12).mpr (Or.inl rfl)
      simp [f4ShortRootSumIndexInv, f4ShortRootSumIndex, h12]
    · have h13 : f4ShortRootWeight 13 = 0 :=
        (f4ShortRootWeight_eq_zero_iff 13).mpr (Or.inr rfl)
      simp [f4ShortRootSumIndexInv, f4ShortRootSumIndex, h13]

/-- **The twenty-six short-root-representation coordinates are the twenty-four short roots and
two zero-weight coordinates.** The zero-weight coordinates `12` and `13` are sent to `0` and `1`
in the `Fin 2` summand, respectively. -/
noncomputable def f4ShortRootWeightIndexEquiv :
    Fin 26 ≃ (F4ShortRootIndex ⊕ Fin 2) :=
  Equiv.mk f4ShortRootSumIndex f4ShortRootSumIndexInv
    f4ShortRootSumIndexInv_apply_f4ShortRootSumIndex
    f4ShortRootSumIndex_apply_f4ShortRootSumIndexInv

@[simp] theorem f4ShortRootWeightIndexEquiv_apply_twelve :
    f4ShortRootWeightIndexEquiv 12 = Sum.inr 0 := by
  have h12 : f4ShortRootWeight 12 = 0 :=
    (f4ShortRootWeight_eq_zero_iff 12).mpr (Or.inl rfl)
  simp [f4ShortRootWeightIndexEquiv, f4ShortRootSumIndex, h12]

@[simp] theorem f4ShortRootWeightIndexEquiv_apply_thirteen :
    f4ShortRootWeightIndexEquiv 13 = Sum.inr 1 := by
  have h13 : f4ShortRootWeight 13 = 0 :=
    (f4ShortRootWeight_eq_zero_iff 13).mpr (Or.inr rfl)
  simp [f4ShortRootWeightIndexEquiv, f4ShortRootSumIndex, h13]

@[simp] theorem f4ShortRootWeight_f4ShortRootWeightIndexEquiv_symm_inl (i : F4ShortRootIndex) :
    f4ShortRootWeight (f4ShortRootWeightIndexEquiv.symm (Sum.inl i)) = f4Root i := by
  simp [f4ShortRootWeightIndexEquiv, f4ShortRootSumIndexInv]

/-- A coordinate index maps to a given short-root label exactly when its weight is that root. -/
@[simp] theorem f4ShortRootWeightIndexEquiv_apply_eq_inl (a : Fin 26)
    (i : F4ShortRootIndex) :
    f4ShortRootWeightIndexEquiv a = Sum.inl i ↔ f4ShortRootWeight a = f4Root i := by
  constructor
  · intro hai
    have ha : a = f4ShortRootWeightIndexEquiv.symm (Sum.inl i) := by
      rw [← hai, Equiv.symm_apply_apply]
    rw [ha, f4ShortRootWeight_f4ShortRootWeightIndexEquiv_symm_inl]
  · intro hweight
    apply f4ShortRootWeightIndexEquiv.symm.injective
    rw [Equiv.symm_apply_apply]
    apply f4ShortRootWeight_injOn
    · change f4ShortRootWeight a ≠ 0
      rw [hweight]
      exact f4Root_ne_zero i
    · change f4ShortRootWeight (f4ShortRootWeightIndexEquiv.symm (Sum.inl i)) ≠ 0
      rw [f4ShortRootWeight_f4ShortRootWeightIndexEquiv_symm_inl]
      exact f4Root_ne_zero i
    · rw [f4ShortRootWeight_f4ShortRootWeightIndexEquiv_symm_inl]
      exact hweight

@[simp] theorem f4ShortRootWeightIndexEquiv_symm_apply_inr_zero :
    f4ShortRootWeightIndexEquiv.symm (Sum.inr 0) = 12 := by
  simp [f4ShortRootWeightIndexEquiv, f4ShortRootSumIndexInv]

@[simp] theorem f4ShortRootWeightIndexEquiv_symm_apply_inr_one :
    f4ShortRootWeightIndexEquiv.symm (Sum.inr 1) = 13 := by
  simp [f4ShortRootWeightIndexEquiv, f4ShortRootSumIndexInv]

/-- Both coordinates in the `Fin 2` summand carry the zero weight. -/
@[simp] theorem f4ShortRootWeight_f4ShortRootWeightIndexEquiv_symm_inr (k : Fin 2) :
    f4ShortRootWeight (f4ShortRootWeightIndexEquiv.symm (Sum.inr k)) = 0 := by
  fin_cases k <;>
    simp [f4ShortRootWeightIndexEquiv, f4ShortRootSumIndexInv,
      f4ShortRootWeight_eq_zero_iff]

/-- The first zero-weight coordinate is the first `Fin 2` summand coordinate. -/
@[simp] theorem f4ShortRootWeightIndexEquiv_apply_eq_inr_zero (a : Fin 26) :
    f4ShortRootWeightIndexEquiv a = Sum.inr 0 ↔ a = 12 := by
  constructor
  · intro h
    apply f4ShortRootWeightIndexEquiv.injective
    simpa using h
  · rintro rfl
    exact f4ShortRootWeightIndexEquiv_apply_twelve

/-- The second zero-weight coordinate is the second `Fin 2` summand coordinate. -/
@[simp] theorem f4ShortRootWeightIndexEquiv_apply_eq_inr_one (a : Fin 26) :
    f4ShortRootWeightIndexEquiv a = Sum.inr 1 ↔ a = 13 := by
  constructor
  · intro h
    apply f4ShortRootWeightIndexEquiv.injective
    simpa using h
  · rintro rfl
    exact f4ShortRootWeightIndexEquiv_apply_thirteen

end TauCeti.DynkinType
