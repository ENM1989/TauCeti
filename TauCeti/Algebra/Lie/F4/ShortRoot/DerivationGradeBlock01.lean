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

private def blockVariables014 : Fin 2 → Fin 26 × Fin 26 :=
  ![(6, 3), (22, 19)]
private def blockConstraints014 : Fin 2 → DerivationConstraint :=
  ![.entry 0 6 19, .entry 1 6 16]
private def blockA014 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 1], ![1, 0]]
private def blockB014 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 1]]

private theorem blockLeftInverse014 : blockB014 * blockA014 = 1 := by
  decide +kernel

private theorem blockSupport014 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-2, 2, -2, 1] k) ↔ ∃ q, blockVariables014 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 14, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock014 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-2, 2, -2, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints014 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables014 q).1 (blockVariables014 q).2
  have hx : blockA014.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA014 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA014, blockConstraints014, DerivationConstraint.evaluate, x,
        blockVariables014, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA014 blockB014
    blockLeftInverse014 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-2, 2, -2, 1]
  · obtain ⟨q, hq'⟩ := (blockSupport014 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables015 : Fin 1 → Fin 26 × Fin 26 :=
  ![(6, 19)]
private def blockConstraints015 : Fin 1 → DerivationConstraint :=
  ![.entry 3 0 19]
private def blockA015 : Matrix (Fin 1) (Fin 1) (ZMod 2) :=
  ![![1]]
private def blockB015 : Matrix (Fin 1) (Fin 1) (ZMod 2) :=
  ![![1]]

private theorem blockLeftInverse015 : blockB015 * blockA015 = 1 := by
  decide +kernel

private theorem blockSupport015 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-2, 2, -2, 2] k) ↔ ∃ q, blockVariables015 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 15, a nonroot degree with 1 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock015 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-2, 2, -2, 2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 1) : (blockConstraints015 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 1 → R := fun q => X (blockVariables015 q).1 (blockVariables015 q).2
  have hx : blockA015.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA015 r i) * x i = 0
    have h := hc r
    fin_cases r; simp [blockA015, blockConstraints015, DerivationConstraint.evaluate, x,
        blockVariables015, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA015 blockB015
    blockLeftInverse015 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-2, 2, -2, 2]
  · obtain ⟨q, hq'⟩ := (blockSupport015 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables016 : Fin 2 → Fin 26 × Fin 26 :=
  ![(9, 3), (22, 16)]
private def blockConstraints016 : Fin 2 → DerivationConstraint :=
  ![.entry 0 6 16, .entry 0 9 19]
private def blockA016 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]
private def blockB016 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]

private theorem blockLeftInverse016 : blockB016 * blockA016 = 1 := by
  decide +kernel

private theorem blockSupport016 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-2, 2, -1, -1] k) ↔ ∃ q, blockVariables016 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 16, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock016 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-2, 2, -1, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints016 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables016 q).1 (blockVariables016 q).2
  have hx : blockA016.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA016 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA016, blockConstraints016, DerivationConstraint.evaluate, x,
        blockVariables016, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA016 blockB016
    blockLeftInverse016 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-2, 2, -1, -1]
  · obtain ⟨q, hq'⟩ := (blockSupport016 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables017 : Fin 2 → Fin 26 × Fin 26 :=
  ![(6, 16), (9, 19)]
private def blockConstraints017 : Fin 2 → DerivationConstraint :=
  ![.entry 3 0 16, .entry 3 1 19]
private def blockA017 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 0], ![0, 1]]
private def blockB017 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 0], ![0, 1]]

private theorem blockLeftInverse017 : blockB017 * blockA017 = 1 := by
  decide +kernel

private theorem blockSupport017 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-2, 2, -1, 0] k) ↔ ∃ q, blockVariables017 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 17, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock017 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-2, 2, -1, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints017 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables017 q).1 (blockVariables017 q).2
  have hx : blockA017.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA017 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA017, blockConstraints017, DerivationConstraint.evaluate, x,
        blockVariables017, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA017 blockB017
    blockLeftInverse017 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-2, 2, -1, 0]
  · obtain ⟨q, hq'⟩ := (blockSupport017 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables018 : Fin 1 → Fin 26 × Fin 26 :=
  ![(9, 16)]
private def blockConstraints018 : Fin 1 → DerivationConstraint :=
  ![.entry 3 1 16]
private def blockA018 : Matrix (Fin 1) (Fin 1) (ZMod 2) :=
  ![![1]]
private def blockB018 : Matrix (Fin 1) (Fin 1) (ZMod 2) :=
  ![![1]]

private theorem blockLeftInverse018 : blockB018 * blockA018 = 1 := by
  decide +kernel

private theorem blockSupport018 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-2, 2, 0, -2] k) ↔ ∃ q, blockVariables018 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 18, a nonroot degree with 1 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock018 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-2, 2, 0, -2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 1) : (blockConstraints018 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 1 → R := fun q => X (blockVariables018 q).1 (blockVariables018 q).2
  have hx : blockA018.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA018 r i) * x i = 0
    have h := hc r
    fin_cases r; simp [blockA018, blockConstraints018, DerivationConstraint.evaluate, x,
        blockVariables018, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA018 blockB018
    blockLeftInverse018 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-2, 2, 0, -2]
  · obtain ⟨q, hq'⟩ := (blockSupport018 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables019 : Fin 2 → Fin 26 × Fin 26 :=
  ![(18, 2), (23, 7)]
private def blockConstraints019 : Fin 2 → DerivationConstraint :=
  ![.entry 0 8 7, .entry 0 18 17]
private def blockA019 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]
private def blockB019 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]

private theorem blockLeftInverse019 : blockB019 * blockA019 = 1 := by
  decide +kernel

private theorem blockSupport019 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-1, -1, 1, 1] k) ↔ ∃ q, blockVariables019 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 19, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock019 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, -1, 1, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints019 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables019 q).1 (blockVariables019 q).2
  have hx : blockA019.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA019 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA019, blockConstraints019, DerivationConstraint.evaluate, x,
        blockVariables019, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA019 blockB019
    blockLeftInverse019 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-1, -1, 1, 1]
  · obtain ⟨q, hq'⟩ := (blockSupport019 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables020 : Fin 2 → Fin 26 × Fin 26 :=
  ![(8, 7), (18, 17)]
private def blockConstraints020 : Fin 2 → DerivationConstraint :=
  ![.entry 1 4 17, .entry 1 8 21]
private def blockA020 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]
private def blockB020 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]

private theorem blockLeftInverse020 : blockB020 * blockA020 = 1 := by
  decide +kernel

private theorem blockSupport020 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-1, -1, 1, 2] k) ↔ ∃ q, blockVariables020 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 20, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock020 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, -1, 1, 2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints020 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables020 q).1 (blockVariables020 q).2
  have hx : blockA020.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA020 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA020, blockConstraints020, DerivationConstraint.evaluate, x,
        blockVariables020, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA020 blockB020
    blockLeftInverse020 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-1, -1, 1, 2]
  · obtain ⟨q, hq'⟩ := (blockSupport020 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables021 : Fin 2 → Fin 26 × Fin 26 :=
  ![(20, 2), (23, 5)]
private def blockConstraints021 : Fin 2 → DerivationConstraint :=
  ![.entry 0 4 2, .entry 0 8 5]
private def blockA021 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 0], ![0, 1]]
private def blockB021 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 0], ![0, 1]]

private theorem blockLeftInverse021 : blockB021 * blockA021 = 1 := by
  decide +kernel

private theorem blockSupport021 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-1, -1, 2, -1] k) ↔ ∃ q, blockVariables021 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 21, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock021 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, -1, 2, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints021 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables021 q).1 (blockVariables021 q).2
  have hx : blockA021.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA021 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA021, blockConstraints021, DerivationConstraint.evaluate, x,
        blockVariables021, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA021 blockB021
    blockLeftInverse021 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-1, -1, 2, -1]
  · obtain ⟨q, hq'⟩ := (blockSupport021 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables022 : Fin 6 → Fin 26 × Fin 26 :=
  ![(4, 2), (8, 5), (11, 7), (18, 14), (20, 17), (23, 21)]
private def blockConstraints022 : Fin 6 → DerivationConstraint :=
  ![.entry 0 4 17, .entry 0 8 21, .entry 1 4 14, .entry 1 11 21, .entry 2 0 5, .quotient 17]
private def blockA022 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ![![1, 0, 0, 0, 1, 0], ![0, 1, 0, 0, 0, 1], ![1, 0, 0, 1, 0, 0], ![0, 0, 1, 0, 0, 1],
      ![1, 1, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0]]
private def blockB022 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 1], ![0, 1, 0, 1, 1, 1], ![0, 0, 1, 0, 0, 1],
      ![1, 0, 0, 0, 0, 1], ![0, 1, 0, 0, 1, 1]]

private theorem blockLeftInverse022 : blockB022 * blockA022 = 1 := by
  decide +kernel

private theorem blockSupport022 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-1, -1, 2, 0] k) ↔ ∃ q, blockVariables022 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 22, a root degree with 6 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock022 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, -1, 2, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 6) : (blockConstraints022 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 6 → R := fun q => X (blockVariables022 q).1 (blockVariables022 q).2
  have hx : blockA022.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA022 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA022, blockConstraints022, DerivationConstraint.evaluate, x,
        blockVariables022, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA022 blockB022
    blockLeftInverse022 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-1, -1, 2, 0]
  · obtain ⟨q, hq'⟩ := (blockSupport022 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables023 : Fin 2 → Fin 26 × Fin 26 :=
  ![(4, 17), (8, 21)]
private def blockConstraints023 : Fin 2 → DerivationConstraint :=
  ![.entry 2 0 21, .entry 2 4 25]
private def blockA023 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]
private def blockB023 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]

private theorem blockLeftInverse023 : blockB023 * blockA023 = 1 := by
  decide +kernel

private theorem blockSupport023 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-1, -1, 2, 1] k) ↔ ∃ q, blockVariables023 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 23, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock023 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, -1, 2, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints023 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables023 q).1 (blockVariables023 q).2
  have hx : blockA023.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA023 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA023, blockConstraints023, DerivationConstraint.evaluate, x,
        blockVariables023, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA023 blockB023
    blockLeftInverse023 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-1, -1, 2, 1]
  · obtain ⟨q, hq'⟩ := (blockSupport023 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables024 : Fin 2 → Fin 26 × Fin 26 :=
  ![(11, 5), (20, 14)]
private def blockConstraints024 : Fin 2 → DerivationConstraint :=
  ![.entry 0 4 14, .entry 0 11 21]
private def blockA024 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]
private def blockB024 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]

private theorem blockLeftInverse024 : blockB024 * blockA024 = 1 := by
  decide +kernel

private theorem blockSupport024 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-1, -1, 3, -2] k) ↔ ∃ q, blockVariables024 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 24, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock024 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, -1, 3, -2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints024 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables024 q).1 (blockVariables024 q).2
  have hx : blockA024.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA024 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA024, blockConstraints024, DerivationConstraint.evaluate, x,
        blockVariables024, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA024 blockB024
    blockLeftInverse024 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-1, -1, 3, -2]
  · obtain ⟨q, hq'⟩ := (blockSupport024 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables025 : Fin 2 → Fin 26 × Fin 26 :=
  ![(4, 14), (11, 21)]
private def blockConstraints025 : Fin 2 → DerivationConstraint :=
  ![.entry 2 1 21, .entry 2 4 24]
private def blockA025 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]
private def blockB025 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]

private theorem blockLeftInverse025 : blockB025 * blockA025 = 1 := by
  decide +kernel

private theorem blockSupport025 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-1, -1, 3, -1] k) ↔ ∃ q, blockVariables025 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 25, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock025 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, -1, 3, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints025 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables025 q).1 (blockVariables025 q).2
  have hx : blockA025.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA025 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA025, blockConstraints025, DerivationConstraint.evaluate, x,
        blockVariables025, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA025 blockB025
    blockLeftInverse025 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-1, -1, 3, -1]
  · obtain ⟨q, hq'⟩ := (blockSupport025 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables026 : Fin 2 → Fin 26 × Fin 26 :=
  ![(18, 1), (24, 7)]
private def blockConstraints026 : Fin 2 → DerivationConstraint :=
  ![.entry 0 10 7, .entry 0 18 15]
private def blockA026 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]
private def blockB026 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]

private theorem blockLeftInverse026 : blockB026 * blockA026 = 1 := by
  decide +kernel

private theorem blockSupport026 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-1, 0, -1, 2] k) ↔ ∃ q, blockVariables026 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 26, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock026 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 0, -1, 2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints026 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables026 q).1 (blockVariables026 q).2
  have hx : blockA026.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA026 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA026, blockConstraints026, DerivationConstraint.evaluate, x,
        blockVariables026, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA026 blockB026
    blockLeftInverse026 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-1, 0, -1, 2]
  · obtain ⟨q, hq'⟩ := (blockSupport026 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables027 : Fin 2 → Fin 26 × Fin 26 :=
  ![(10, 7), (18, 15)]
private def blockConstraints027 : Fin 2 → DerivationConstraint :=
  ![.entry 1 0 7, .entry 1 4 15]
private def blockA027 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 0], ![0, 1]]
private def blockB027 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 0], ![0, 1]]

private theorem blockLeftInverse027 : blockB027 * blockA027 = 1 := by
  decide +kernel

private theorem blockSupport027 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-1, 0, -1, 3] k) ↔ ∃ q, blockVariables027 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 27, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock027 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 0, -1, 3] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints027 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables027 q).1 (blockVariables027 q).2
  have hx : blockA027.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA027 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA027, blockConstraints027, DerivationConstraint.evaluate, x,
        blockVariables027, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA027 blockB027
    blockLeftInverse027 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-1, 0, -1, 3]
  · obtain ⟨q, hq'⟩ := (blockSupport027 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd


end TauCeti.F4ShortRoot
