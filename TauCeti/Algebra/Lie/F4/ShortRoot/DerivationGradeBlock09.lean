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

private def blockVariables126 : Fin 2 → Fin 26 × Fin 26 :=
  ![(0, 22), (3, 25)]
private def blockConstraints126 : Fin 2 → DerivationConstraint :=
  ![.entry 6 0 25, .entry 9 0 24]
private def blockA126 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 1], ![1, 0]]
private def blockB126 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 1]]

private theorem blockLeftInverse126 : blockB126 * blockA126 = 1 := by
  decide +kernel

private theorem blockSupport126 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![1, -1, 1, 1] k) ↔ ∃ q, blockVariables126 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 126, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock126 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, -1, 1, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints126 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables126 q).1 (blockVariables126 q).2
  have hx : blockA126.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA126 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA126, blockConstraints126, DerivationConstraint.evaluate, x,
        blockVariables126, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA126 blockB126
    blockLeftInverse126 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![1, -1, 1, 1]
  · obtain ⟨q, hq'⟩ := (blockSupport126 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables127 : Fin 2 → Fin 26 × Fin 26 :=
  ![(15, 6), (19, 10)]
private def blockConstraints127 : Fin 2 → DerivationConstraint :=
  ![.entry 0 1 6, .entry 0 3 10]
private def blockA127 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 0], ![0, 1]]
private def blockB127 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 0], ![0, 1]]

private theorem blockLeftInverse127 : blockB127 * blockA127 = 1 := by
  decide +kernel

private theorem blockSupport127 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![1, -1, 2, -3] k) ↔ ∃ q, blockVariables127 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 127, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock127 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, -1, 2, -3] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints127 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables127 q).1 (blockVariables127 q).2
  have hx : blockA127.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA127 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA127, blockConstraints127, DerivationConstraint.evaluate, x,
        blockVariables127, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA127 blockB127
    blockLeftInverse127 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![1, -1, 2, -3]
  · obtain ⟨q, hq'⟩ := (blockSupport127 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables128 : Fin 6 → Fin 26 × Fin 26 :=
  ![(1, 6), (3, 10), (7, 14), (11, 18), (15, 22), (19, 24)]
private def blockConstraints128 : Fin 6 → DerivationConstraint :=
  ![.entry 0 1 22, .entry 0 3 24, .entry 2 1 18, .entry 2 7 24, .entry 4 1 14, .quotient 6]
private def blockA128 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ![![1, 0, 0, 0, 1, 0], ![0, 1, 0, 0, 0, 1], ![1, 0, 0, 1, 0, 0], ![0, 0, 1, 0, 0, 1],
      ![1, 0, 1, 0, 0, 0], ![1, 0, 0, 0, 0, 0]]
private def blockB128 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 1], ![0, 1, 0, 1, 1, 1], ![0, 0, 0, 0, 1, 1], ![0, 0, 1, 0, 0, 1],
      ![1, 0, 0, 0, 0, 1], ![0, 0, 0, 1, 1, 1]]

private theorem blockLeftInverse128 : blockB128 * blockA128 = 1 := by
  decide +kernel

private theorem blockSupport128 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![1, -1, 2, -2] k) ↔ ∃ q, blockVariables128 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 128, a root degree with 6 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock128 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, -1, 2, -2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 6) : (blockConstraints128 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 6 → R := fun q => X (blockVariables128 q).1 (blockVariables128 q).2
  have hx : blockA128.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA128 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA128, blockConstraints128, DerivationConstraint.evaluate, x,
        blockVariables128, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA128 blockB128
    blockLeftInverse128 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![1, -1, 2, -2]
  · obtain ⟨q, hq'⟩ := (blockSupport128 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables129 : Fin 2 → Fin 26 × Fin 26 :=
  ![(1, 22), (3, 24)]
private def blockConstraints129 : Fin 2 → DerivationConstraint :=
  ![.entry 6 0 24, .entry 6 1 25]
private def blockA129 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]
private def blockB129 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]

private theorem blockLeftInverse129 : blockB129 * blockA129 = 1 := by
  decide +kernel

private theorem blockSupport129 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![1, -1, 2, -1] k) ↔ ∃ q, blockVariables129 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 129, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock129 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, -1, 2, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints129 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables129 q).1 (blockVariables129 q).2
  have hx : blockA129.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA129 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA129, blockConstraints129, DerivationConstraint.evaluate, x,
        blockVariables129, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA129 blockB129
    blockLeftInverse129 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![1, -1, 2, -1]
  · obtain ⟨q, hq'⟩ := (blockSupport129 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables130 : Fin 2 → Fin 26 × Fin 26 :=
  ![(21, 1), (24, 4)]
private def blockConstraints130 : Fin 2 → DerivationConstraint :=
  ![.entry 0 5 1, .entry 0 10 4]
private def blockA130 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 0], ![0, 1]]
private def blockB130 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 0], ![0, 1]]

private theorem blockLeftInverse130 : blockB130 * blockA130 = 1 := by
  decide +kernel

private theorem blockSupport130 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![1, 0, -2, 1] k) ↔ ∃ q, blockVariables130 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 130, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock130 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, 0, -2, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints130 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables130 q).1 (blockVariables130 q).2
  have hx : blockA130.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA130 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA130, blockConstraints130, DerivationConstraint.evaluate, x,
        blockVariables130, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA130 blockB130
    blockLeftInverse130 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![1, 0, -2, 1]
  · obtain ⟨q, hq'⟩ := (blockSupport130 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables131 : Fin 6 → Fin 26 × Fin 26 :=
  ![(5, 1), (10, 4), (14, 9), (16, 11), (21, 15), (24, 20)]
private def blockConstraints131 : Fin 6 → DerivationConstraint :=
  ![.entry 0 5 15, .entry 0 10 20, .entry 1 0 4, .entry 1 2 9, .entry 1 3 11, .quotient 16]
private def blockA131 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ![![1, 0, 0, 0, 1, 0], ![0, 1, 0, 0, 0, 1], ![1, 1, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0],
      ![1, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 0, 0]]
private def blockB131 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 1], ![0, 0, 1, 0, 0, 1], ![0, 0, 0, 1, 0, 1], ![0, 0, 0, 0, 1, 1],
      ![1, 0, 0, 0, 0, 1], ![0, 1, 1, 0, 0, 1]]

private theorem blockLeftInverse131 : blockB131 * blockA131 = 1 := by
  decide +kernel

private theorem blockSupport131 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![1, 0, -2, 2] k) ↔ ∃ q, blockVariables131 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 131, a root degree with 6 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock131 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, 0, -2, 2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 6) : (blockConstraints131 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 6 → R := fun q => X (blockVariables131 q).1 (blockVariables131 q).2
  have hx : blockA131.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA131 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA131, blockConstraints131, DerivationConstraint.evaluate, x,
        blockVariables131, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA131 blockB131
    blockLeftInverse131 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![1, 0, -2, 2]
  · obtain ⟨q, hq'⟩ := (blockSupport131 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables132 : Fin 2 → Fin 26 × Fin 26 :=
  ![(5, 15), (10, 20)]
private def blockConstraints132 : Fin 2 → DerivationConstraint :=
  ![.entry 1 0 20, .entry 1 5 25]
private def blockA132 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]
private def blockB132 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]

private theorem blockLeftInverse132 : blockB132 * blockA132 = 1 := by
  decide +kernel

private theorem blockSupport132 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![1, 0, -2, 3] k) ↔ ∃ q, blockVariables132 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 132, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock132 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, 0, -2, 3] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints132 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables132 q).1 (blockVariables132 q).2
  have hx : blockA132.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA132 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA132, blockConstraints132, DerivationConstraint.evaluate, x,
        blockVariables132, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA132 blockB132
    blockLeftInverse132 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![1, 0, -2, 3]
  · obtain ⟨q, hq'⟩ := (blockSupport132 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables133 : Fin 2 → Fin 26 × Fin 26 :=
  ![(21, 0), (25, 4)]
private def blockConstraints133 : Fin 2 → DerivationConstraint :=
  ![.entry 0 7 1, .entry 0 12 4]
private def blockA133 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 0], ![0, 1]]
private def blockB133 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 0], ![0, 1]]

private theorem blockLeftInverse133 : blockB133 * blockA133 = 1 := by
  decide +kernel

private theorem blockSupport133 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![1, 0, -1, -1] k) ↔ ∃ q, blockVariables133 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 133, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock133 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, 0, -1, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints133 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables133 q).1 (blockVariables133 q).2
  have hx : blockA133.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA133 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA133, blockConstraints133, DerivationConstraint.evaluate, x,
        blockVariables133, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA133 blockB133
    blockLeftInverse133 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![1, 0, -1, -1]
  · obtain ⟨q, hq'⟩ := (blockSupport133 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables134 : Fin 12 → Fin 26 × Fin 26 :=
  ![(5, 0), (7, 1), (12, 4), (13, 4), (14, 6), (16, 8), (17, 9), (19, 11), (21, 12), (21, 13),
      (24, 18), (25, 20)]
private def blockConstraints134 : Fin 12 → DerivationConstraint :=
  ![.entry 0 0 4, .entry 0 2 9, .entry 0 3 11, .entry 0 5 12, .entry 0 5 13, .entry 0 7 15,
      .entry 0 10 18, .entry 0 12 20, .entry 0 14 22, .entry 0 16 23, .entry 1 1 4, .ideal 21]
private def blockA134 : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ![![1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
      ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      ![0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
private def blockB134 : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1],
      ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1],
      ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1], ![1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 1]]

private theorem blockLeftInverse134 : blockB134 * blockA134 = 1 := by
  decide +kernel

private theorem blockSupport134 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![1, 0, -1, 0] k) ↔ ∃ q, blockVariables134 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 134, a root degree with 12 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock134 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, 0, -1, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 12) : (blockConstraints134 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 12 → R := fun q => X (blockVariables134 q).1 (blockVariables134 q).2
  have hx : blockA134.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA134 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA134, blockConstraints134, DerivationConstraint.evaluate, x,
        blockVariables134, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA134 blockB134
    blockLeftInverse134 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![1, 0, -1, 0]
  · obtain ⟨q, hq'⟩ := (blockSupport134 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables135 : Fin 12 → Fin 26 × Fin 26 :=
  ![(0, 4), (2, 9), (3, 11), (5, 12), (5, 13), (7, 15), (10, 18), (12, 20), (13, 20), (14, 22),
      (16, 23), (21, 25)]
private def blockConstraints135 : Fin 12 → DerivationConstraint :=
  ![.entry 0 0 20, .entry 0 5 25, .entry 1 0 18, .entry 1 1 20, .entry 1 2 22, .entry 1 3 23,
      .entry 1 5 24, .entry 1 7 25, .entry 2 2 20, .entry 2 5 23, .entry 3 3 20, .ideal 5]
private def blockA135 : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ![![1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
      ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0],
      ![0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0],
      ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1],
      ![0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0],
      ![0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
private def blockB135 : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1],
      ![1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1], ![1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 1],
      ![1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 1], ![1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1],
      ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
      ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1],
      ![1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1], ![1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 1]]

private theorem blockLeftInverse135 : blockB135 * blockA135 = 1 := by
  decide +kernel

private theorem blockSupport135 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![1, 0, -1, 1] k) ↔ ∃ q, blockVariables135 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 135, a root degree with 12 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock135 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, 0, -1, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 12) : (blockConstraints135 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 12 → R := fun q => X (blockVariables135 q).1 (blockVariables135 q).2
  have hx : blockA135.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA135 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA135, blockConstraints135, DerivationConstraint.evaluate, x,
        blockVariables135, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA135 blockB135
    blockLeftInverse135 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![1, 0, -1, 1]
  · obtain ⟨q, hq'⟩ := (blockSupport135 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables136 : Fin 2 → Fin 26 × Fin 26 :=
  ![(0, 20), (5, 25)]
private def blockConstraints136 : Fin 2 → DerivationConstraint :=
  ![.entry 4 0 25, .entry 9 0 23]
private def blockA136 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 1], ![1, 0]]
private def blockB136 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 1]]

private theorem blockLeftInverse136 : blockB136 * blockA136 = 1 := by
  decide +kernel

private theorem blockSupport136 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![1, 0, -1, 2] k) ↔ ∃ q, blockVariables136 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 136, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock136 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, 0, -1, 2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints136 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables136 q).1 (blockVariables136 q).2
  have hx : blockA136.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA136 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA136, blockConstraints136, DerivationConstraint.evaluate, x,
        blockVariables136, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA136 blockB136
    blockLeftInverse136 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![1, 0, -1, 2]
  · obtain ⟨q, hq'⟩ := (blockSupport136 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables137 : Fin 6 → Fin 26 × Fin 26 :=
  ![(7, 0), (15, 4), (17, 6), (19, 8), (21, 10), (25, 18)]
private def blockConstraints137 : Fin 6 → DerivationConstraint :=
  ![.entry 0 1 4, .entry 0 2 6, .entry 0 3 8, .entry 0 5 10, .entry 0 12 18, .quotient 18]
private def blockA137 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ![![1, 1, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0],
      ![1, 0, 0, 0, 0, 1], ![1, 0, 0, 0, 0, 0]]
private def blockB137 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 1], ![1, 0, 0, 0, 0, 1], ![0, 1, 0, 0, 0, 1], ![0, 0, 1, 0, 0, 1],
      ![0, 0, 0, 1, 0, 1], ![0, 0, 0, 0, 1, 1]]

private theorem blockLeftInverse137 : blockB137 * blockA137 = 1 := by
  decide +kernel

private theorem blockSupport137 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![1, 0, 0, -2] k) ↔ ∃ q, blockVariables137 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 137, a root degree with 6 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock137 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, 0, 0, -2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 6) : (blockConstraints137 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 6 → R := fun q => X (blockVariables137 q).1 (blockVariables137 q).2
  have hx : blockA137.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA137 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA137, blockConstraints137, DerivationConstraint.evaluate, x,
        blockVariables137, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA137 blockB137
    blockLeftInverse137 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![1, 0, 0, -2]
  · obtain ⟨q, hq'⟩ := (blockSupport137 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables138 : Fin 12 → Fin 26 × Fin 26 :=
  ![(1, 4), (2, 6), (3, 8), (5, 10), (7, 12), (7, 13), (12, 18), (13, 18), (15, 20), (17, 22),
      (19, 23), (21, 24)]
private def blockConstraints138 : Fin 12 → DerivationConstraint :=
  ![.entry 0 0 18, .entry 0 1 20, .entry 0 2 22, .entry 0 3 23, .entry 0 5 24, .entry 0 7 25,
      .entry 1 1 18, .entry 1 7 24, .entry 2 2 18, .entry 2 7 23, .entry 3 3 18, .ideal 7]
private def blockA138 : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
      ![0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0],
      ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
      ![1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1],
      ![0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0],
      ![0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
private def blockB138 : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1],
      ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1], ![1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1],
      ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 1],
      ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1],
      ![1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 1], ![1, 0, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1]]

private theorem blockLeftInverse138 : blockB138 * blockA138 = 1 := by
  decide +kernel

private theorem blockSupport138 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![1, 0, 0, -1] k) ↔ ∃ q, blockVariables138 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 138, a root degree with 12 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock138 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, 0, 0, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 12) : (blockConstraints138 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 12 → R := fun q => X (blockVariables138 q).1 (blockVariables138 q).2
  have hx : blockA138.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA138 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA138, blockConstraints138, DerivationConstraint.evaluate, x,
        blockVariables138, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA138 blockB138
    blockLeftInverse138 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![1, 0, 0, -1]
  · obtain ⟨q, hq'⟩ := (blockSupport138 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables139 : Fin 6 → Fin 26 × Fin 26 :=
  ![(0, 18), (1, 20), (2, 22), (3, 23), (5, 24), (7, 25)]
private def blockConstraints139 : Fin 6 → DerivationConstraint :=
  ![.entry 4 0 24, .entry 4 1 25, .entry 6 0 23, .entry 6 2 25, .entry 8 0 22, .quotient 0]
private def blockA139 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ![![1, 0, 0, 0, 1, 0], ![0, 1, 0, 0, 0, 1], ![1, 0, 0, 1, 0, 0], ![0, 0, 1, 0, 0, 1],
      ![1, 0, 1, 0, 0, 0], ![1, 0, 0, 0, 0, 0]]
private def blockB139 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 1], ![0, 1, 0, 1, 1, 1], ![0, 0, 0, 0, 1, 1], ![0, 0, 1, 0, 0, 1],
      ![1, 0, 0, 0, 0, 1], ![0, 0, 0, 1, 1, 1]]

private theorem blockLeftInverse139 : blockB139 * blockA139 = 1 := by
  decide +kernel

private theorem blockSupport139 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![1, 0, 0, 0] k) ↔ ∃ q, blockVariables139 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 139, a root degree with 6 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock139 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, 0, 0, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 6) : (blockConstraints139 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 6 → R := fun q => X (blockVariables139 q).1 (blockVariables139 q).2
  have hx : blockA139.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA139 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA139, blockConstraints139, DerivationConstraint.evaluate, x,
        blockVariables139, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA139 blockB139
    blockLeftInverse139 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![1, 0, 0, 0]
  · obtain ⟨q, hq'⟩ := (blockSupport139 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd


end TauCeti.F4ShortRoot
