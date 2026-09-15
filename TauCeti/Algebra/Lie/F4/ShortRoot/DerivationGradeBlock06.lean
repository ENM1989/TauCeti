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

private def blockVariables084 : Fin 12 → Fin 26 × Fin 26 :=
  ![(0, 12), (0, 13), (1, 15), (2, 17), (3, 19), (4, 20), (5, 21), (6, 22), (8, 23), (10, 24),
      (12, 25), (13, 25)]
private def blockConstraints084 : Fin 12 → DerivationConstraint :=
  ![.entry 0 0 25, .entry 1 0 24, .entry 1 1 25, .entry 2 0 23, .entry 2 2 25, .entry 3 0 22,
      .entry 3 3 25, .entry 4 0 21, .entry 4 4 25, .entry 5 0 20, .entry 7 0 18, .ideal 0]
private def blockA084 : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1], ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
      ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0], ![0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0], ![1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
private def blockB084 : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      ![1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 1], ![0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 1],
      ![0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1],
      ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1],
      ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
      ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]]

private theorem blockLeftInverse084 : blockB084 * blockA084 = 1 := by
  decide +kernel

private theorem blockSupport084 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![0, 0, 0, 1] k) ↔ ∃ q, blockVariables084 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 84, a root degree with 12 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock084 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 0, 0, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 12) : (blockConstraints084 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 12 → R := fun q => X (blockVariables084 q).1 (blockVariables084 q).2
  have hx : blockA084.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA084 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA084, blockConstraints084, DerivationConstraint.evaluate, x,
        blockVariables084, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA084 blockB084
    blockLeftInverse084 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![0, 0, 0, 1]
  · obtain ⟨q, hq'⟩ := (blockSupport084 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables085 : Fin 1 → Fin 26 × Fin 26 :=
  ![(0, 25)]
private def blockConstraints085 : Fin 1 → DerivationConstraint :=
  ![.entry 15 0 24]
private def blockA085 : Matrix (Fin 1) (Fin 1) (ZMod 2) :=
  ![![1]]
private def blockB085 : Matrix (Fin 1) (Fin 1) (ZMod 2) :=
  ![![1]]

private theorem blockLeftInverse085 : blockB085 * blockA085 = 1 := by
  decide +kernel

private theorem blockSupport085 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![0, 0, 0, 2] k) ↔ ∃ q, blockVariables085 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 85, a nonroot degree with 1 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock085 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 0, 0, 2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 1) : (blockConstraints085 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 1 → R := fun q => X (blockVariables085 q).1 (blockVariables085 q).2
  have hx : blockA085.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA085 r i) * x i = 0
    have h := hc r
    fin_cases r; simp [blockA085, blockConstraints085, DerivationConstraint.evaluate, x,
        blockVariables085, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA085 blockB085
    blockLeftInverse085 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![0, 0, 0, 2]
  · obtain ⟨q, hq'⟩ := (blockSupport085 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables086 : Fin 2 → Fin 26 × Fin 26 :=
  ![(15, 0), (25, 10)]
private def blockConstraints086 : Fin 2 → DerivationConstraint :=
  ![.entry 0 7 5, .entry 0 12 10]
private def blockA086 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 0], ![0, 1]]
private def blockB086 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 0], ![0, 1]]

private theorem blockLeftInverse086 : blockB086 * blockA086 = 1 := by
  decide +kernel

private theorem blockSupport086 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![0, 0, 1, -3] k) ↔ ∃ q, blockVariables086 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 86, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock086 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 0, 1, -3] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints086 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables086 q).1 (blockVariables086 q).2
  have hx : blockA086.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA086 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA086, blockConstraints086, DerivationConstraint.evaluate, x,
        blockVariables086, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA086 blockB086
    blockLeftInverse086 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![0, 0, 1, -3]
  · obtain ⟨q, hq'⟩ := (blockSupport086 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables087 : Fin 12 → Fin 26 × Fin 26 :=
  ![(1, 0), (7, 5), (9, 6), (11, 8), (12, 10), (13, 10), (15, 12), (15, 13), (17, 14),
      (19, 16), (20, 18), (25, 24)]
private def blockConstraints087 : Fin 12 → DerivationConstraint :=
  ![.entry 0 0 10, .entry 0 1 12, .entry 0 1 13, .entry 0 2 14, .entry 0 3 16, .entry 0 4 18,
      .entry 0 7 21, .entry 0 9 22, .entry 0 11 23, .entry 0 12 24, .entry 1 1 10, .ideal 15]
private def blockA087 : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ![![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
      ![1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
      ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1],
      ![1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
private def blockB087 : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1],
      ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1],
      ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1],
      ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1]]

private theorem blockLeftInverse087 : blockB087 * blockA087 = 1 := by
  decide +kernel

private theorem blockSupport087 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![0, 0, 1, -2] k) ↔ ∃ q, blockVariables087 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 87, a root degree with 12 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock087 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 0, 1, -2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 12) : (blockConstraints087 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 12 → R := fun q => X (blockVariables087 q).1 (blockVariables087 q).2
  have hx : blockA087.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA087 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA087, blockConstraints087, DerivationConstraint.evaluate, x,
        blockVariables087, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA087 blockB087
    blockLeftInverse087 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![0, 0, 1, -2]
  · obtain ⟨q, hq'⟩ := (blockSupport087 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables088 : Fin 12 → Fin 26 × Fin 26 :=
  ![(0, 10), (1, 12), (1, 13), (2, 14), (3, 16), (4, 18), (7, 21), (9, 22), (11, 23), (12, 24),
      (13, 24), (15, 25)]
private def blockConstraints088 : Fin 12 → DerivationConstraint :=
  ![.entry 0 0 24, .entry 0 1 25, .entry 1 1 24, .entry 2 1 23, .entry 2 2 24, .entry 3 1 22,
      .entry 3 3 24, .entry 4 1 21, .entry 4 4 24, .entry 5 0 18, .entry 5 2 22, .ideal 1]
private def blockA088 : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      ![0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0],
      ![0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      ![0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
private def blockB088 : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1],
      ![0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1], ![0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1],
      ![0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1],
      ![0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1], ![0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 1],
      ![0, 0, 0, 1, 1, 1, 0, 0, 1, 1, 1, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1],
      ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1]]

private theorem blockLeftInverse088 : blockB088 * blockA088 = 1 := by
  decide +kernel

private theorem blockSupport088 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![0, 0, 1, -1] k) ↔ ∃ q, blockVariables088 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 88, a root degree with 12 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock088 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 0, 1, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 12) : (blockConstraints088 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 12 → R := fun q => X (blockVariables088 q).1 (blockVariables088 q).2
  have hx : blockA088.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA088 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA088, blockConstraints088, DerivationConstraint.evaluate, x,
        blockVariables088, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA088 blockB088
    blockLeftInverse088 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![0, 0, 1, -1]
  · obtain ⟨q, hq'⟩ := (blockSupport088 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables089 : Fin 2 → Fin 26 × Fin 26 :=
  ![(0, 24), (1, 25)]
private def blockConstraints089 : Fin 2 → DerivationConstraint :=
  ![.entry 10 0 25, .entry 12 0 24]
private def blockA089 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 1], ![1, 0]]
private def blockB089 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 1]]

private theorem blockLeftInverse089 : blockB089 * blockA089 = 1 := by
  decide +kernel

private theorem blockSupport089 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![0, 0, 1, 0] k) ↔ ∃ q, blockVariables089 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 89, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock089 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 0, 1, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints089 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables089 q).1 (blockVariables089 q).2
  have hx : blockA089.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA089 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA089, blockConstraints089, DerivationConstraint.evaluate, x,
        blockVariables089, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA089 blockB089
    blockLeftInverse089 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![0, 0, 1, 0]
  · obtain ⟨q, hq'⟩ := (blockSupport089 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables090 : Fin 1 → Fin 26 × Fin 26 :=
  ![(15, 10)]
private def blockConstraints090 : Fin 1 → DerivationConstraint :=
  ![.entry 0 1 10]
private def blockA090 : Matrix (Fin 1) (Fin 1) (ZMod 2) :=
  ![![1]]
private def blockB090 : Matrix (Fin 1) (Fin 1) (ZMod 2) :=
  ![![1]]

private theorem blockLeftInverse090 : blockB090 * blockA090 = 1 := by
  decide +kernel

private theorem blockSupport090 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![0, 0, 2, -4] k) ↔ ∃ q, blockVariables090 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 90, a nonroot degree with 1 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock090 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 0, 2, -4] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 1) : (blockConstraints090 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 1 → R := fun q => X (blockVariables090 q).1 (blockVariables090 q).2
  have hx : blockA090.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA090 r i) * x i = 0
    have h := hc r
    fin_cases r; simp [blockA090, blockConstraints090, DerivationConstraint.evaluate, x,
        blockVariables090, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA090 blockB090
    blockLeftInverse090 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![0, 0, 2, -4]
  · obtain ⟨q, hq'⟩ := (blockSupport090 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables091 : Fin 2 → Fin 26 × Fin 26 :=
  ![(1, 10), (15, 24)]
private def blockConstraints091 : Fin 2 → DerivationConstraint :=
  ![.entry 0 1 24, .entry 5 1 18]
private def blockA091 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 1], ![1, 0]]
private def blockB091 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 1]]

private theorem blockLeftInverse091 : blockB091 * blockA091 = 1 := by
  decide +kernel

private theorem blockSupport091 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![0, 0, 2, -3] k) ↔ ∃ q, blockVariables091 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 91, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock091 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 0, 2, -3] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints091 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables091 q).1 (blockVariables091 q).2
  have hx : blockA091.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA091 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA091, blockConstraints091, DerivationConstraint.evaluate, x,
        blockVariables091, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA091 blockB091
    blockLeftInverse091 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![0, 0, 2, -3]
  · obtain ⟨q, hq'⟩ := (blockSupport091 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables092 : Fin 1 → Fin 26 × Fin 26 :=
  ![(1, 24)]
private def blockConstraints092 : Fin 1 → DerivationConstraint :=
  ![.entry 10 0 24]
private def blockA092 : Matrix (Fin 1) (Fin 1) (ZMod 2) :=
  ![![1]]
private def blockB092 : Matrix (Fin 1) (Fin 1) (ZMod 2) :=
  ![![1]]

private theorem blockLeftInverse092 : blockB092 * blockA092 = 1 := by
  decide +kernel

private theorem blockSupport092 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![0, 0, 2, -2] k) ↔ ∃ q, blockVariables092 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 92, a nonroot degree with 1 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock092 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 0, 2, -2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 1) : (blockConstraints092 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 1 → R := fun q => X (blockVariables092 q).1 (blockVariables092 q).2
  have hx : blockA092.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA092 r i) * x i = 0
    have h := hc r
    fin_cases r; simp [blockA092, blockConstraints092, DerivationConstraint.evaluate, x,
        blockVariables092, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA092 blockB092
    blockLeftInverse092 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![0, 0, 2, -2]
  · obtain ⟨q, hq'⟩ := (blockSupport092 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables093 : Fin 2 → Fin 26 × Fin 26 :=
  ![(14, 1), (24, 11)]
private def blockConstraints093 : Fin 2 → DerivationConstraint :=
  ![.entry 0 10 11, .entry 0 14 15]
private def blockA093 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]
private def blockB093 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]

private theorem blockLeftInverse093 : blockB093 * blockA093 = 1 := by
  decide +kernel

private theorem blockSupport093 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![0, 1, -3, 2] k) ↔ ∃ q, blockVariables093 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 93, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock093 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 1, -3, 2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints093 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables093 q).1 (blockVariables093 q).2
  have hx : blockA093.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA093 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA093, blockConstraints093, DerivationConstraint.evaluate, x,
        blockVariables093, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA093 blockB093
    blockLeftInverse093 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![0, 1, -3, 2]
  · obtain ⟨q, hq'⟩ := (blockSupport093 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables094 : Fin 2 → Fin 26 × Fin 26 :=
  ![(10, 11), (14, 15)]
private def blockConstraints094 : Fin 2 → DerivationConstraint :=
  ![.entry 1 0 11, .entry 1 2 15]
private def blockA094 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 0], ![0, 1]]
private def blockB094 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 0], ![0, 1]]

private theorem blockLeftInverse094 : blockB094 * blockA094 = 1 := by
  decide +kernel

private theorem blockSupport094 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![0, 1, -3, 3] k) ↔ ∃ q, blockVariables094 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 94, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock094 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 1, -3, 3] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints094 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables094 q).1 (blockVariables094 q).2
  have hx : blockA094.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA094 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA094, blockConstraints094, DerivationConstraint.evaluate, x,
        blockVariables094, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA094 blockB094
    blockLeftInverse094 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![0, 1, -3, 3]
  · obtain ⟨q, hq'⟩ := (blockSupport094 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables095 : Fin 6 → Fin 26 × Fin 26 :=
  ![(14, 0), (17, 1), (21, 3), (22, 4), (24, 8), (25, 11)]
private def blockConstraints095 : Fin 6 → DerivationConstraint :=
  ![.entry 0 2 1, .entry 0 5 3, .entry 0 6 4, .entry 0 10 8, .entry 0 12 11, .quotient 23]
private def blockA095 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ![![1, 1, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0],
      ![1, 0, 0, 0, 0, 1], ![1, 0, 0, 0, 0, 0]]
private def blockB095 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 1], ![1, 0, 0, 0, 0, 1], ![0, 1, 0, 0, 0, 1], ![0, 0, 1, 0, 0, 1],
      ![0, 0, 0, 1, 0, 1], ![0, 0, 0, 0, 1, 1]]

private theorem blockLeftInverse095 : blockB095 * blockA095 = 1 := by
  decide +kernel

private theorem blockSupport095 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![0, 1, -2, 0] k) ↔ ∃ q, blockVariables095 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 95, a root degree with 6 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock095 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 1, -2, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 6) : (blockConstraints095 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 6 → R := fun q => X (blockVariables095 q).1 (blockVariables095 q).2
  have hx : blockA095.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA095 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA095, blockConstraints095, DerivationConstraint.evaluate, x,
        blockVariables095, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA095 blockB095
    blockLeftInverse095 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![0, 1, -2, 0]
  · obtain ⟨q, hq'⟩ := (blockSupport095 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables096 : Fin 12 → Fin 26 × Fin 26 :=
  ![(2, 1), (5, 3), (6, 4), (10, 8), (12, 11), (13, 11), (14, 12), (14, 13), (17, 15),
      (21, 19), (22, 20), (24, 23)]
private def blockConstraints096 : Fin 12 → DerivationConstraint :=
  ![.entry 0 0 11, .entry 0 2 15, .entry 0 5 19, .entry 0 6 20, .entry 0 10 23, .entry 0 14 25,
      .entry 1 0 8, .entry 1 1 11, .entry 1 2 13, .entry 1 5 16, .entry 1 6 18, .ideal 14]
private def blockA096 : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
      ![0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0],
      ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
      ![1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0],
      ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
private def blockB096 : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1],
      ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1],
      ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1],
      ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1], ![0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1]]

private theorem blockLeftInverse096 : blockB096 * blockA096 = 1 := by
  decide +kernel

private theorem blockSupport096 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![0, 1, -2, 1] k) ↔ ∃ q, blockVariables096 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 96, a root degree with 12 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock096 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 1, -2, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 12) : (blockConstraints096 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 12 → R := fun q => X (blockVariables096 q).1 (blockVariables096 q).2
  have hx : blockA096.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA096 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA096, blockConstraints096, DerivationConstraint.evaluate, x,
        blockVariables096, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA096 blockB096
    blockLeftInverse096 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![0, 1, -2, 1]
  · obtain ⟨q, hq'⟩ := (blockSupport096 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables097 : Fin 6 → Fin 26 × Fin 26 :=
  ![(0, 11), (2, 15), (5, 19), (6, 20), (10, 23), (14, 25)]
private def blockConstraints097 : Fin 6 → DerivationConstraint :=
  ![.entry 1 0 23, .entry 1 2 25, .entry 3 0 20, .entry 3 5 25, .entry 4 0 19, .quotient 3]
private def blockA097 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ![![1, 0, 0, 0, 1, 0], ![0, 1, 0, 0, 0, 1], ![1, 0, 0, 1, 0, 0], ![0, 0, 1, 0, 0, 1],
      ![1, 0, 1, 0, 0, 0], ![1, 0, 0, 0, 0, 0]]
private def blockB097 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 1], ![0, 1, 0, 1, 1, 1], ![0, 0, 0, 0, 1, 1], ![0, 0, 1, 0, 0, 1],
      ![1, 0, 0, 0, 0, 1], ![0, 0, 0, 1, 1, 1]]

private theorem blockLeftInverse097 : blockB097 * blockA097 = 1 := by
  decide +kernel

private theorem blockSupport097 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![0, 1, -2, 2] k) ↔ ∃ q, blockVariables097 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 97, a root degree with 6 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock097 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 1, -2, 2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 6) : (blockConstraints097 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 6 → R := fun q => X (blockVariables097 q).1 (blockVariables097 q).2
  have hx : blockA097.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA097 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA097, blockConstraints097, DerivationConstraint.evaluate, x,
        blockVariables097, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA097 blockB097
    blockLeftInverse097 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![0, 1, -2, 2]
  · obtain ⟨q, hq'⟩ := (blockSupport097 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd


end TauCeti.F4ShortRoot
