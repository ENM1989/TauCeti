/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.CharTwoLinearAlgebra
public import TauCeti.Algebra.Lie.F4.ShortRoot.DerivationConstraint

/-!
# Certified nonzero homogeneous blocks for type-F4 derivations

This generated shard records small binary left-inverse certificates. Lean checks each certificate
against the explicit derivation equations and replays it over every characteristic-two ring.
-/

public section

open Matrix

namespace TauCeti.F4ShortRoot

universe u

variable {R : Type u} [CommRing R] [CharP R 2]

set_option linter.unusedSimpArgs false

private def blockVariables000 : Fin 1 → Fin 26 × Fin 26 :=
  ![(18, 7)]
private def blockConstraints000 : Fin 1 → DerivationConstraint :=
  ![.entry 1 4 7]
private def blockA000 : Matrix (Fin 1) (Fin 1) (ZMod 2) :=
  ![![1]]
private def blockB000 : Matrix (Fin 1) (Fin 1) (ZMod 2) :=
  ![![1]]

private theorem blockLeftInverse000 : blockB000 * blockA000 = 1 := by
  decide +kernel

private theorem blockSupport000 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-2, 0, 0, 2] k) ↔ ∃ q, blockVariables000 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 0, a nonroot degree with 1 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock000 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-2, 0, 0, 2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 1) : (blockConstraints000 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 1 → R := fun q => X (blockVariables000 q).1 (blockVariables000 q).2
  have hx : blockA000.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA000 r i) * x i = 0
    have h := hc r
    fin_cases r; simp [blockA000, blockConstraints000, DerivationConstraint.evaluate, x,
        blockVariables000, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA000 blockB000
    blockLeftInverse000 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-2, 0, 0, 2]
  · obtain ⟨q, hq'⟩ := (blockSupport000 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables001 : Fin 2 → Fin 26 × Fin 26 :=
  ![(18, 5), (20, 7)]
private def blockConstraints001 : Fin 2 → DerivationConstraint :=
  ![.entry 0 4 7, .entry 0 18 21]
private def blockA001 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]
private def blockB001 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]

private theorem blockLeftInverse001 : blockB001 * blockA001 = 1 := by
  decide +kernel

private theorem blockSupport001 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-2, 0, 1, 0] k) ↔ ∃ q, blockVariables001 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 1, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock001 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-2, 0, 1, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints001 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables001 q).1 (blockVariables001 q).2
  have hx : blockA001.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA001 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA001, blockConstraints001, DerivationConstraint.evaluate, x,
        blockVariables001, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA001 blockB001
    blockLeftInverse001 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-2, 0, 1, 0]
  · obtain ⟨q, hq'⟩ := (blockSupport001 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables002 : Fin 2 → Fin 26 × Fin 26 :=
  ![(4, 7), (18, 21)]
private def blockConstraints002 : Fin 2 → DerivationConstraint :=
  ![.entry 1 4 21, .entry 2 4 19]
private def blockA002 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 1], ![1, 0]]
private def blockB002 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 1]]

private theorem blockLeftInverse002 : blockB002 * blockA002 = 1 := by
  decide +kernel

private theorem blockSupport002 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-2, 0, 1, 1] k) ↔ ∃ q, blockVariables002 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 2, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock002 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-2, 0, 1, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints002 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables002 q).1 (blockVariables002 q).2
  have hx : blockA002.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA002 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA002, blockConstraints002, DerivationConstraint.evaluate, x,
        blockVariables002, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA002 blockB002
    blockLeftInverse002 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-2, 0, 1, 1]
  · obtain ⟨q, hq'⟩ := (blockSupport002 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables003 : Fin 1 → Fin 26 × Fin 26 :=
  ![(20, 5)]
private def blockConstraints003 : Fin 1 → DerivationConstraint :=
  ![.entry 0 4 5]
private def blockA003 : Matrix (Fin 1) (Fin 1) (ZMod 2) :=
  ![![1]]
private def blockB003 : Matrix (Fin 1) (Fin 1) (ZMod 2) :=
  ![![1]]

private theorem blockLeftInverse003 : blockB003 * blockA003 = 1 := by
  decide +kernel

private theorem blockSupport003 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-2, 0, 2, -2] k) ↔ ∃ q, blockVariables003 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 3, a nonroot degree with 1 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock003 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-2, 0, 2, -2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 1) : (blockConstraints003 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 1 → R := fun q => X (blockVariables003 q).1 (blockVariables003 q).2
  have hx : blockA003.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA003 r i) * x i = 0
    have h := hc r
    fin_cases r; simp [blockA003, blockConstraints003, DerivationConstraint.evaluate, x,
        blockVariables003, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA003 blockB003
    blockLeftInverse003 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-2, 0, 2, -2]
  · obtain ⟨q, hq'⟩ := (blockSupport003 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables004 : Fin 2 → Fin 26 × Fin 26 :=
  ![(4, 5), (20, 21)]
private def blockConstraints004 : Fin 2 → DerivationConstraint :=
  ![.entry 0 4 21, .entry 2 4 16]
private def blockA004 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 1], ![1, 0]]
private def blockB004 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 1]]

private theorem blockLeftInverse004 : blockB004 * blockA004 = 1 := by
  decide +kernel

private theorem blockSupport004 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-2, 0, 2, -1] k) ↔ ∃ q, blockVariables004 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 4, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock004 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-2, 0, 2, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints004 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables004 q).1 (blockVariables004 q).2
  have hx : blockA004.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA004 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA004, blockConstraints004, DerivationConstraint.evaluate, x,
        blockVariables004, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA004 blockB004
    blockLeftInverse004 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-2, 0, 2, -1]
  · obtain ⟨q, hq'⟩ := (blockSupport004 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables005 : Fin 1 → Fin 26 × Fin 26 :=
  ![(4, 21)]
private def blockConstraints005 : Fin 1 → DerivationConstraint :=
  ![.entry 5 0 21]
private def blockA005 : Matrix (Fin 1) (Fin 1) (ZMod 2) :=
  ![![1]]
private def blockB005 : Matrix (Fin 1) (Fin 1) (ZMod 2) :=
  ![![1]]

private theorem blockLeftInverse005 : blockB005 * blockA005 = 1 := by
  decide +kernel

private theorem blockSupport005 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-2, 0, 2, 0] k) ↔ ∃ q, blockVariables005 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 5, a nonroot degree with 1 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock005 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-2, 0, 2, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 1) : (blockConstraints005 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 1 → R := fun q => X (blockVariables005 q).1 (blockVariables005 q).2
  have hx : blockA005.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA005 r i) * x i = 0
    have h := hc r
    fin_cases r; simp [blockA005, blockConstraints005, DerivationConstraint.evaluate, x,
        blockVariables005, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA005 blockB005
    blockLeftInverse005 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-2, 0, 2, 0]
  · obtain ⟨q, hq'⟩ := (blockSupport005 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables006 : Fin 2 → Fin 26 × Fin 26 :=
  ![(18, 3), (22, 7)]
private def blockConstraints006 : Fin 2 → DerivationConstraint :=
  ![.entry 0 6 7, .entry 0 18 19]
private def blockA006 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]
private def blockB006 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]

private theorem blockLeftInverse006 : blockB006 * blockA006 = 1 := by
  decide +kernel

private theorem blockSupport006 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-2, 1, -1, 1] k) ↔ ∃ q, blockVariables006 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 6, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock006 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-2, 1, -1, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints006 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables006 q).1 (blockVariables006 q).2
  have hx : blockA006.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA006 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA006, blockConstraints006, DerivationConstraint.evaluate, x,
        blockVariables006, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA006 blockB006
    blockLeftInverse006 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-2, 1, -1, 1]
  · obtain ⟨q, hq'⟩ := (blockSupport006 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables007 : Fin 2 → Fin 26 × Fin 26 :=
  ![(6, 7), (18, 19)]
private def blockConstraints007 : Fin 2 → DerivationConstraint :=
  ![.entry 1 4 19, .entry 1 6 21]
private def blockA007 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]
private def blockB007 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]

private theorem blockLeftInverse007 : blockB007 * blockA007 = 1 := by
  decide +kernel

private theorem blockSupport007 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-2, 1, -1, 2] k) ↔ ∃ q, blockVariables007 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 7, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock007 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-2, 1, -1, 2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints007 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables007 q).1 (blockVariables007 q).2
  have hx : blockA007.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA007 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA007, blockConstraints007, DerivationConstraint.evaluate, x,
        blockVariables007, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA007 blockB007
    blockLeftInverse007 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-2, 1, -1, 2]
  · obtain ⟨q, hq'⟩ := (blockSupport007 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables008 : Fin 2 → Fin 26 × Fin 26 :=
  ![(20, 3), (22, 5)]
private def blockConstraints008 : Fin 2 → DerivationConstraint :=
  ![.entry 0 4 3, .entry 0 6 5]
private def blockA008 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 0], ![0, 1]]
private def blockB008 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 0], ![0, 1]]

private theorem blockLeftInverse008 : blockB008 * blockA008 = 1 := by
  decide +kernel

private theorem blockSupport008 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-2, 1, 0, -1] k) ↔ ∃ q, blockVariables008 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 8, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock008 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-2, 1, 0, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints008 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables008 q).1 (blockVariables008 q).2
  have hx : blockA008.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA008 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA008, blockConstraints008, DerivationConstraint.evaluate, x,
        blockVariables008, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA008 blockB008
    blockLeftInverse008 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-2, 1, 0, -1]
  · obtain ⟨q, hq'⟩ := (blockSupport008 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables009 : Fin 6 → Fin 26 × Fin 26 :=
  ![(4, 3), (6, 5), (9, 7), (18, 16), (20, 19), (22, 21)]
private def blockConstraints009 : Fin 6 → DerivationConstraint :=
  ![.entry 0 4 19, .entry 0 6 21, .entry 1 4 16, .entry 1 9 21, .entry 2 6 16, .quotient 15]
private def blockA009 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ![![1, 0, 0, 0, 1, 0], ![0, 1, 0, 0, 0, 1], ![1, 0, 0, 1, 0, 0], ![0, 0, 1, 0, 0, 1],
      ![0, 1, 0, 1, 0, 0], ![1, 0, 0, 0, 0, 0]]
private def blockB009 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 1], ![0, 0, 1, 0, 1, 1], ![0, 1, 1, 1, 1, 1], ![0, 0, 1, 0, 0, 1],
      ![1, 0, 0, 0, 0, 1], ![0, 1, 1, 0, 1, 1]]

private theorem blockLeftInverse009 : blockB009 * blockA009 = 1 := by
  decide +kernel

private theorem blockSupport009 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-2, 1, 0, 0] k) ↔ ∃ q, blockVariables009 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 9, a root degree with 6 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock009 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-2, 1, 0, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 6) : (blockConstraints009 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 6 → R := fun q => X (blockVariables009 q).1 (blockVariables009 q).2
  have hx : blockA009.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA009 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA009, blockConstraints009, DerivationConstraint.evaluate, x,
        blockVariables009, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA009 blockB009
    blockLeftInverse009 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-2, 1, 0, 0]
  · obtain ⟨q, hq'⟩ := (blockSupport009 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables010 : Fin 2 → Fin 26 × Fin 26 :=
  ![(4, 19), (6, 21)]
private def blockConstraints010 : Fin 2 → DerivationConstraint :=
  ![.entry 3 0 21, .entry 3 4 25]
private def blockA010 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]
private def blockB010 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]

private theorem blockLeftInverse010 : blockB010 * blockA010 = 1 := by
  decide +kernel

private theorem blockSupport010 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-2, 1, 0, 1] k) ↔ ∃ q, blockVariables010 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 10, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock010 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-2, 1, 0, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints010 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables010 q).1 (blockVariables010 q).2
  have hx : blockA010.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA010 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA010, blockConstraints010, DerivationConstraint.evaluate, x,
        blockVariables010, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA010 blockB010
    blockLeftInverse010 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-2, 1, 0, 1]
  · obtain ⟨q, hq'⟩ := (blockSupport010 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables011 : Fin 2 → Fin 26 × Fin 26 :=
  ![(9, 5), (20, 16)]
private def blockConstraints011 : Fin 2 → DerivationConstraint :=
  ![.entry 0 4 16, .entry 0 9 21]
private def blockA011 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]
private def blockB011 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]

private theorem blockLeftInverse011 : blockB011 * blockA011 = 1 := by
  decide +kernel

private theorem blockSupport011 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-2, 1, 1, -2] k) ↔ ∃ q, blockVariables011 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 11, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock011 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-2, 1, 1, -2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints011 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables011 q).1 (blockVariables011 q).2
  have hx : blockA011.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA011 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA011, blockConstraints011, DerivationConstraint.evaluate, x,
        blockVariables011, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA011 blockB011
    blockLeftInverse011 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-2, 1, 1, -2]
  · obtain ⟨q, hq'⟩ := (blockSupport011 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables012 : Fin 2 → Fin 26 × Fin 26 :=
  ![(4, 16), (9, 21)]
private def blockConstraints012 : Fin 2 → DerivationConstraint :=
  ![.entry 3 1 21, .entry 3 4 24]
private def blockA012 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]
private def blockB012 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]

private theorem blockLeftInverse012 : blockB012 * blockA012 = 1 := by
  decide +kernel

private theorem blockSupport012 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-2, 1, 1, -1] k) ↔ ∃ q, blockVariables012 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 12, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock012 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-2, 1, 1, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints012 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables012 q).1 (blockVariables012 q).2
  have hx : blockA012.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA012 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA012, blockConstraints012, DerivationConstraint.evaluate, x,
        blockVariables012, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA012 blockB012
    blockLeftInverse012 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-2, 1, 1, -1]
  · obtain ⟨q, hq'⟩ := (blockSupport012 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables013 : Fin 1 → Fin 26 × Fin 26 :=
  ![(22, 3)]
private def blockConstraints013 : Fin 1 → DerivationConstraint :=
  ![.entry 0 6 3]
private def blockA013 : Matrix (Fin 1) (Fin 1) (ZMod 2) :=
  ![![1]]
private def blockB013 : Matrix (Fin 1) (Fin 1) (ZMod 2) :=
  ![![1]]

private theorem blockLeftInverse013 : blockB013 * blockA013 = 1 := by
  decide +kernel

private theorem blockSupport013 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-2, 2, -2, 0] k) ↔ ∃ q, blockVariables013 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 13, a nonroot degree with 1 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock013 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-2, 2, -2, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 1) : (blockConstraints013 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 1 → R := fun q => X (blockVariables013 q).1 (blockVariables013 q).2
  have hx : blockA013.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA013 r i) * x i = 0
    have h := hc r
    fin_cases r; simp [blockA013, blockConstraints013, DerivationConstraint.evaluate, x,
        blockVariables013, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA013 blockB013
    blockLeftInverse013 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-2, 2, -2, 0]
  · obtain ⟨q, hq'⟩ := (blockSupport013 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd


end TauCeti.F4ShortRoot
