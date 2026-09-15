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

private def blockVariables098 : Fin 2 → Fin 26 × Fin 26 :=
  ![(17, 0), (25, 8)]
private def blockConstraints098 : Fin 2 → DerivationConstraint :=
  ![.entry 0 7 3, .entry 0 12 8]
private def blockA098 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 0], ![1, 1]]
private def blockB098 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 0], ![1, 1]]

private theorem blockLeftInverse098 : blockB098 * blockA098 = 1 := by
  decide +kernel

private theorem blockSupport098 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![0, 1, -1, -2] k) ↔ ∃ q, blockVariables098 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 98, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock098 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 1, -1, -2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints098 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables098 q).1 (blockVariables098 q).2
  have hx : blockA098.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA098 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA098, blockConstraints098, DerivationConstraint.evaluate, x,
        blockVariables098, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA098 blockB098
    blockLeftInverse098 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![0, 1, -1, -2]
  · obtain ⟨q, hq'⟩ := (blockSupport098 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables099 : Fin 12 → Fin 26 × Fin 26 :=
  ![(2, 0), (7, 3), (9, 4), (12, 8), (13, 8), (14, 10), (15, 11), (17, 12), (17, 13), (21, 16),
      (22, 18), (25, 23)]
private def blockConstraints099 : Fin 12 → DerivationConstraint :=
  ![.entry 0 0 8, .entry 0 1 11, .entry 0 2 12, .entry 0 2 13, .entry 0 5 16, .entry 0 6 18,
      .entry 0 7 19, .entry 0 9 20, .entry 0 12 23, .entry 0 14 24, .entry 1 1 8, .ideal 17]
private def blockA099 : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ![![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
      ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
      ![1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
      ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
private def blockB099 : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1],
      ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
      ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1],
      ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1],
      ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1], ![1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1]]

private theorem blockLeftInverse099 : blockB099 * blockA099 = 1 := by
  decide +kernel

private theorem blockSupport099 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![0, 1, -1, -1] k) ↔ ∃ q, blockVariables099 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 99, a root degree with 12 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock099 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 1, -1, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 12) : (blockConstraints099 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 12 → R := fun q => X (blockVariables099 q).1 (blockVariables099 q).2
  have hx : blockA099.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA099 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA099, blockConstraints099, DerivationConstraint.evaluate, x,
        blockVariables099, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA099 blockB099
    blockLeftInverse099 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![0, 1, -1, -1]
  · obtain ⟨q, hq'⟩ := (blockSupport099 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables100 : Fin 12 → Fin 26 × Fin 26 :=
  ![(0, 8), (1, 11), (2, 12), (2, 13), (5, 16), (6, 18), (7, 19), (9, 20), (12, 23), (13, 23),
      (14, 24), (17, 25)]
private def blockConstraints100 : Fin 12 → DerivationConstraint :=
  ![.entry 0 0 23, .entry 0 2 25, .entry 1 1 23, .entry 1 2 24, .entry 2 2 23, .entry 3 0 18,
      .entry 3 1 20, .entry 3 2 22, .entry 3 5 24, .entry 3 7 25, .entry 4 0 16, .ideal 2]
private def blockA100 : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      ![0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0], ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0],
      ![0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0], ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      ![0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1],
      ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
private def blockB100 : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1],
      ![0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 1], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1],
      ![0, 1, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1], ![1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 1],
      ![0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1], ![0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 1, 1]]

private theorem blockLeftInverse100 : blockB100 * blockA100 = 1 := by
  decide +kernel

private theorem blockSupport100 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![0, 1, -1, 0] k) ↔ ∃ q, blockVariables100 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 100, a root degree with 12 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock100 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 1, -1, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 12) : (blockConstraints100 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 12 → R := fun q => X (blockVariables100 q).1 (blockVariables100 q).2
  have hx : blockA100.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA100 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA100, blockConstraints100, DerivationConstraint.evaluate, x,
        blockVariables100, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA100 blockB100
    blockLeftInverse100 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![0, 1, -1, 0]
  · obtain ⟨q, hq'⟩ := (blockSupport100 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables101 : Fin 2 → Fin 26 × Fin 26 :=
  ![(0, 23), (2, 25)]
private def blockConstraints101 : Fin 2 → DerivationConstraint :=
  ![.entry 8 0 25, .entry 11 0 24]
private def blockA101 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 1], ![1, 0]]
private def blockB101 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 1]]

private theorem blockLeftInverse101 : blockB101 * blockA101 = 1 := by
  decide +kernel

private theorem blockSupport101 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![0, 1, -1, 1] k) ↔ ∃ q, blockVariables101 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 101, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock101 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 1, -1, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints101 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables101 q).1 (blockVariables101 q).2
  have hx : blockA101.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA101 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA101, blockConstraints101, DerivationConstraint.evaluate, x,
        blockVariables101, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA101 blockB101
    blockLeftInverse101 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![0, 1, -1, 1]
  · obtain ⟨q, hq'⟩ := (blockSupport101 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables102 : Fin 2 → Fin 26 × Fin 26 :=
  ![(15, 8), (17, 10)]
private def blockConstraints102 : Fin 2 → DerivationConstraint :=
  ![.entry 0 1 8, .entry 0 2 10]
private def blockA102 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 0], ![0, 1]]
private def blockB102 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 0], ![0, 1]]

private theorem blockLeftInverse102 : blockB102 * blockA102 = 1 := by
  decide +kernel

private theorem blockSupport102 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![0, 1, 0, -3] k) ↔ ∃ q, blockVariables102 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 102, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock102 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 1, 0, -3] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints102 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables102 q).1 (blockVariables102 q).2
  have hx : blockA102.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA102 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA102, blockConstraints102, DerivationConstraint.evaluate, x,
        blockVariables102, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA102 blockB102
    blockLeftInverse102 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![0, 1, 0, -3]
  · obtain ⟨q, hq'⟩ := (blockSupport102 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables103 : Fin 6 → Fin 26 × Fin 26 :=
  ![(1, 8), (2, 10), (7, 16), (9, 18), (15, 23), (17, 24)]
private def blockConstraints103 : Fin 6 → DerivationConstraint :=
  ![.entry 0 1 23, .entry 0 2 24, .entry 3 1 18, .entry 3 7 24, .entry 4 1 16, .quotient 4]
private def blockA103 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ![![1, 0, 0, 0, 1, 0], ![0, 1, 0, 0, 0, 1], ![1, 0, 0, 1, 0, 0], ![0, 0, 1, 0, 0, 1],
      ![1, 0, 1, 0, 0, 0], ![1, 0, 0, 0, 0, 0]]
private def blockB103 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 1], ![0, 1, 0, 1, 1, 1], ![0, 0, 0, 0, 1, 1], ![0, 0, 1, 0, 0, 1],
      ![1, 0, 0, 0, 0, 1], ![0, 0, 0, 1, 1, 1]]

private theorem blockLeftInverse103 : blockB103 * blockA103 = 1 := by
  decide +kernel

private theorem blockSupport103 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![0, 1, 0, -2] k) ↔ ∃ q, blockVariables103 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 103, a root degree with 6 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock103 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 1, 0, -2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 6) : (blockConstraints103 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 6 → R := fun q => X (blockVariables103 q).1 (blockVariables103 q).2
  have hx : blockA103.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA103 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA103, blockConstraints103, DerivationConstraint.evaluate, x,
        blockVariables103, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA103 blockB103
    blockLeftInverse103 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![0, 1, 0, -2]
  · obtain ⟨q, hq'⟩ := (blockSupport103 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables104 : Fin 2 → Fin 26 × Fin 26 :=
  ![(1, 23), (2, 24)]
private def blockConstraints104 : Fin 2 → DerivationConstraint :=
  ![.entry 8 0 24, .entry 8 1 25]
private def blockA104 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]
private def blockB104 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]

private theorem blockLeftInverse104 : blockB104 * blockA104 = 1 := by
  decide +kernel

private theorem blockSupport104 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![0, 1, 0, -1] k) ↔ ∃ q, blockVariables104 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 104, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock104 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 1, 0, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints104 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables104 q).1 (blockVariables104 q).2
  have hx : blockA104.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA104 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA104, blockConstraints104, DerivationConstraint.evaluate, x,
        blockVariables104, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA104 blockB104
    blockLeftInverse104 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![0, 1, 0, -1]
  · obtain ⟨q, hq'⟩ := (blockSupport104 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables105 : Fin 1 → Fin 26 × Fin 26 :=
  ![(14, 11)]
private def blockConstraints105 : Fin 1 → DerivationConstraint :=
  ![.entry 1 2 11]
private def blockA105 : Matrix (Fin 1) (Fin 1) (ZMod 2) :=
  ![![1]]
private def blockB105 : Matrix (Fin 1) (Fin 1) (ZMod 2) :=
  ![![1]]

private theorem blockLeftInverse105 : blockB105 * blockA105 = 1 := by
  decide +kernel

private theorem blockSupport105 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![0, 2, -4, 2] k) ↔ ∃ q, blockVariables105 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 105, a nonroot degree with 1 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock105 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 2, -4, 2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 1) : (blockConstraints105 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 1 → R := fun q => X (blockVariables105 q).1 (blockVariables105 q).2
  have hx : blockA105.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA105 r i) * x i = 0
    have h := hc r
    fin_cases r; simp [blockA105, blockConstraints105, DerivationConstraint.evaluate, x,
        blockVariables105, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA105 blockB105
    blockLeftInverse105 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![0, 2, -4, 2]
  · obtain ⟨q, hq'⟩ := (blockSupport105 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables106 : Fin 2 → Fin 26 × Fin 26 :=
  ![(14, 8), (17, 11)]
private def blockConstraints106 : Fin 2 → DerivationConstraint :=
  ![.entry 0 2 11, .entry 0 14 23]
private def blockA106 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]
private def blockB106 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]

private theorem blockLeftInverse106 : blockB106 * blockA106 = 1 := by
  decide +kernel

private theorem blockSupport106 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![0, 2, -3, 0] k) ↔ ∃ q, blockVariables106 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 106, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock106 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 2, -3, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints106 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables106 q).1 (blockVariables106 q).2
  have hx : blockA106.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA106 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA106, blockConstraints106, DerivationConstraint.evaluate, x,
        blockVariables106, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA106 blockB106
    blockLeftInverse106 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![0, 2, -3, 0]
  · obtain ⟨q, hq'⟩ := (blockSupport106 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables107 : Fin 2 → Fin 26 × Fin 26 :=
  ![(2, 11), (14, 23)]
private def blockConstraints107 : Fin 2 → DerivationConstraint :=
  ![.entry 1 2 23, .entry 3 2 20]
private def blockA107 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 1], ![1, 0]]
private def blockB107 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 1]]

private theorem blockLeftInverse107 : blockB107 * blockA107 = 1 := by
  decide +kernel

private theorem blockSupport107 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![0, 2, -3, 1] k) ↔ ∃ q, blockVariables107 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 107, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock107 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 2, -3, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints107 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables107 q).1 (blockVariables107 q).2
  have hx : blockA107.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA107 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA107, blockConstraints107, DerivationConstraint.evaluate, x,
        blockVariables107, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA107 blockB107
    blockLeftInverse107 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![0, 2, -3, 1]
  · obtain ⟨q, hq'⟩ := (blockSupport107 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables108 : Fin 1 → Fin 26 × Fin 26 :=
  ![(17, 8)]
private def blockConstraints108 : Fin 1 → DerivationConstraint :=
  ![.entry 0 2 8]
private def blockA108 : Matrix (Fin 1) (Fin 1) (ZMod 2) :=
  ![![1]]
private def blockB108 : Matrix (Fin 1) (Fin 1) (ZMod 2) :=
  ![![1]]

private theorem blockLeftInverse108 : blockB108 * blockA108 = 1 := by
  decide +kernel

private theorem blockSupport108 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![0, 2, -2, -2] k) ↔ ∃ q, blockVariables108 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 108, a nonroot degree with 1 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock108 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 2, -2, -2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 1) : (blockConstraints108 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 1 → R := fun q => X (blockVariables108 q).1 (blockVariables108 q).2
  have hx : blockA108.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA108 r i) * x i = 0
    have h := hc r
    fin_cases r; simp [blockA108, blockConstraints108, DerivationConstraint.evaluate, x,
        blockVariables108, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA108 blockB108
    blockLeftInverse108 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![0, 2, -2, -2]
  · obtain ⟨q, hq'⟩ := (blockSupport108 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables109 : Fin 2 → Fin 26 × Fin 26 :=
  ![(2, 8), (17, 23)]
private def blockConstraints109 : Fin 2 → DerivationConstraint :=
  ![.entry 0 2 23, .entry 3 2 18]
private def blockA109 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 1], ![1, 0]]
private def blockB109 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 1]]

private theorem blockLeftInverse109 : blockB109 * blockA109 = 1 := by
  decide +kernel

private theorem blockSupport109 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![0, 2, -2, -1] k) ↔ ∃ q, blockVariables109 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 109, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock109 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 2, -2, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints109 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables109 q).1 (blockVariables109 q).2
  have hx : blockA109.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA109 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA109, blockConstraints109, DerivationConstraint.evaluate, x,
        blockVariables109, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA109 blockB109
    blockLeftInverse109 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![0, 2, -2, -1]
  · obtain ⟨q, hq'⟩ := (blockSupport109 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables110 : Fin 1 → Fin 26 × Fin 26 :=
  ![(2, 23)]
private def blockConstraints110 : Fin 1 → DerivationConstraint :=
  ![.entry 8 0 23]
private def blockA110 : Matrix (Fin 1) (Fin 1) (ZMod 2) :=
  ![![1]]
private def blockB110 : Matrix (Fin 1) (Fin 1) (ZMod 2) :=
  ![![1]]

private theorem blockLeftInverse110 : blockB110 * blockA110 = 1 := by
  decide +kernel

private theorem blockSupport110 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![0, 2, -2, 0] k) ↔ ∃ q, blockVariables110 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 110, a nonroot degree with 1 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock110 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 2, -2, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 1) : (blockConstraints110 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 1 → R := fun q => X (blockVariables110 q).1 (blockVariables110 q).2
  have hx : blockA110.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA110 r i) * x i = 0
    have h := hc r
    fin_cases r; simp [blockA110, blockConstraints110, DerivationConstraint.evaluate, x,
        blockVariables110, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA110 blockB110
    blockLeftInverse110 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![0, 2, -2, 0]
  · obtain ⟨q, hq'⟩ := (blockSupport110 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables111 : Fin 2 → Fin 26 × Fin 26 :=
  ![(16, 2), (23, 9)]
private def blockConstraints111 : Fin 2 → DerivationConstraint :=
  ![.entry 0 8 9, .entry 0 16 17]
private def blockA111 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]
private def blockB111 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]

private theorem blockLeftInverse111 : blockB111 * blockA111 = 1 := by
  decide +kernel

private theorem blockSupport111 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![1, -2, 1, 1] k) ↔ ∃ q, blockVariables111 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 111, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock111 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, -2, 1, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints111 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables111 q).1 (blockVariables111 q).2
  have hx : blockA111.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA111 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA111, blockConstraints111, DerivationConstraint.evaluate, x,
        blockVariables111, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA111 blockB111
    blockLeftInverse111 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![1, -2, 1, 1]
  · obtain ⟨q, hq'⟩ := (blockSupport111 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd


end TauCeti.F4ShortRoot
