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

private def blockVariables070 : Fin 6 → Fin 26 × Fin 26 :=
  ![(11, 0), (15, 2), (19, 5), (20, 6), (23, 10), (25, 14)]
private def blockConstraints070 : Fin 6 → DerivationConstraint :=
  ![.entry 0 1 2, .entry 0 3 5, .entry 0 4 6, .entry 0 8 10, .entry 0 12 14, .quotient 22]
private def blockA070 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ![![1, 1, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0],
      ![1, 0, 0, 0, 0, 1], ![1, 0, 0, 0, 0, 0]]
private def blockB070 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 1], ![1, 0, 0, 0, 0, 1], ![0, 1, 0, 0, 0, 1], ![0, 0, 1, 0, 0, 1],
      ![0, 0, 0, 1, 0, 1], ![0, 0, 0, 0, 1, 1]]

private theorem blockLeftInverse070 : blockB070 * blockA070 = 1 := by
  decide +kernel

private theorem blockSupport070 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![0, -1, 2, -2] k) ↔ ∃ q, blockVariables070 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 70, a root degree with 6 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock070 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, -1, 2, -2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 6) : (blockConstraints070 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 6 → R := fun q => X (blockVariables070 q).1 (blockVariables070 q).2
  have hx : blockA070.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA070 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA070, blockConstraints070, DerivationConstraint.evaluate, x,
        blockVariables070, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA070 blockB070
    blockLeftInverse070 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![0, -1, 2, -2]
  · obtain ⟨q, hq'⟩ := (blockSupport070 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables071 : Fin 12 → Fin 26 × Fin 26 :=
  ![(1, 2), (3, 5), (4, 6), (8, 10), (11, 12), (11, 13), (12, 14), (13, 14), (15, 17),
      (19, 21), (20, 22), (23, 24)]
private def blockConstraints071 : Fin 12 → DerivationConstraint :=
  ![.entry 0 0 14, .entry 0 1 17, .entry 0 3 21, .entry 0 4 22, .entry 0 8 24, .entry 0 11 25,
      .entry 1 1 14, .entry 1 11 24, .entry 2 0 10, .entry 2 3 16, .entry 2 4 18, .ideal 11]
private def blockA071 : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
      ![0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0],
      ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
      ![1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1],
      ![1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
private def blockB071 : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1],
      ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1],
      ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1],
      ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1], ![0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1]]

private theorem blockLeftInverse071 : blockB071 * blockA071 = 1 := by
  decide +kernel

private theorem blockSupport071 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![0, -1, 2, -1] k) ↔ ∃ q, blockVariables071 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 71, a root degree with 12 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock071 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, -1, 2, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 12) : (blockConstraints071 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 12 → R := fun q => X (blockVariables071 q).1 (blockVariables071 q).2
  have hx : blockA071.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA071 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA071, blockConstraints071, DerivationConstraint.evaluate, x,
        blockVariables071, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA071 blockB071
    blockLeftInverse071 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![0, -1, 2, -1]
  · obtain ⟨q, hq'⟩ := (blockSupport071 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables072 : Fin 6 → Fin 26 × Fin 26 :=
  ![(0, 14), (1, 17), (3, 21), (4, 22), (8, 24), (11, 25)]
private def blockConstraints072 : Fin 6 → DerivationConstraint :=
  ![.entry 2 0 24, .entry 2 1 25, .entry 5 0 22, .entry 5 3 25, .entry 6 0 21, .quotient 2]
private def blockA072 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ![![1, 0, 0, 0, 1, 0], ![0, 1, 0, 0, 0, 1], ![1, 0, 0, 1, 0, 0], ![0, 0, 1, 0, 0, 1],
      ![1, 0, 1, 0, 0, 0], ![1, 0, 0, 0, 0, 0]]
private def blockB072 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 1], ![0, 1, 0, 1, 1, 1], ![0, 0, 0, 0, 1, 1], ![0, 0, 1, 0, 0, 1],
      ![1, 0, 0, 0, 0, 1], ![0, 0, 0, 1, 1, 1]]

private theorem blockLeftInverse072 : blockB072 * blockA072 = 1 := by
  decide +kernel

private theorem blockSupport072 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![0, -1, 2, 0] k) ↔ ∃ q, blockVariables072 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 72, a root degree with 6 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock072 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, -1, 2, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 6) : (blockConstraints072 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 6 → R := fun q => X (blockVariables072 q).1 (blockVariables072 q).2
  have hx : blockA072.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA072 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA072, blockConstraints072, DerivationConstraint.evaluate, x,
        blockVariables072, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA072 blockB072
    blockLeftInverse072 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![0, -1, 2, 0]
  · obtain ⟨q, hq'⟩ := (blockSupport072 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables073 : Fin 2 → Fin 26 × Fin 26 :=
  ![(11, 10), (15, 14)]
private def blockConstraints073 : Fin 2 → DerivationConstraint :=
  ![.entry 0 1 14, .entry 0 11 24]
private def blockA073 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]
private def blockB073 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]

private theorem blockLeftInverse073 : blockB073 * blockA073 = 1 := by
  decide +kernel

private theorem blockSupport073 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![0, -1, 3, -3] k) ↔ ∃ q, blockVariables073 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 73, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock073 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, -1, 3, -3] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints073 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables073 q).1 (blockVariables073 q).2
  have hx : blockA073.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA073 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA073, blockConstraints073, DerivationConstraint.evaluate, x,
        blockVariables073, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA073 blockB073
    blockLeftInverse073 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![0, -1, 3, -3]
  · obtain ⟨q, hq'⟩ := (blockSupport073 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables074 : Fin 2 → Fin 26 × Fin 26 :=
  ![(1, 14), (11, 24)]
private def blockConstraints074 : Fin 2 → DerivationConstraint :=
  ![.entry 2 1 24, .entry 5 1 22]
private def blockA074 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 1], ![1, 0]]
private def blockB074 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 1]]

private theorem blockLeftInverse074 : blockB074 * blockA074 = 1 := by
  decide +kernel

private theorem blockSupport074 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![0, -1, 3, -2] k) ↔ ∃ q, blockVariables074 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 74, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock074 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, -1, 3, -2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints074 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables074 q).1 (blockVariables074 q).2
  have hx : blockA074.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA074 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA074, blockConstraints074, DerivationConstraint.evaluate, x,
        blockVariables074, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA074 blockB074
    blockLeftInverse074 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![0, -1, 3, -2]
  · obtain ⟨q, hq'⟩ := (blockSupport074 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables075 : Fin 1 → Fin 26 × Fin 26 :=
  ![(24, 1)]
private def blockConstraints075 : Fin 1 → DerivationConstraint :=
  ![.entry 0 10 1]
private def blockA075 : Matrix (Fin 1) (Fin 1) (ZMod 2) :=
  ![![1]]
private def blockB075 : Matrix (Fin 1) (Fin 1) (ZMod 2) :=
  ![![1]]

private theorem blockLeftInverse075 : blockB075 * blockA075 = 1 := by
  decide +kernel

private theorem blockSupport075 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![0, 0, -2, 2] k) ↔ ∃ q, blockVariables075 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 75, a nonroot degree with 1 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock075 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 0, -2, 2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 1) : (blockConstraints075 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 1 → R := fun q => X (blockVariables075 q).1 (blockVariables075 q).2
  have hx : blockA075.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA075 r i) * x i = 0
    have h := hc r
    fin_cases r; simp [blockA075, blockConstraints075, DerivationConstraint.evaluate, x,
        blockVariables075, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA075 blockB075
    blockLeftInverse075 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![0, 0, -2, 2]
  · obtain ⟨q, hq'⟩ := (blockSupport075 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables076 : Fin 2 → Fin 26 × Fin 26 :=
  ![(10, 1), (24, 15)]
private def blockConstraints076 : Fin 2 → DerivationConstraint :=
  ![.entry 0 10 15, .entry 1 5 7]
private def blockA076 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 1], ![1, 0]]
private def blockB076 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 1]]

private theorem blockLeftInverse076 : blockB076 * blockA076 = 1 := by
  decide +kernel

private theorem blockSupport076 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![0, 0, -2, 3] k) ↔ ∃ q, blockVariables076 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 76, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock076 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 0, -2, 3] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints076 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables076 q).1 (blockVariables076 q).2
  have hx : blockA076.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA076 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA076, blockConstraints076, DerivationConstraint.evaluate, x,
        blockVariables076, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA076 blockB076
    blockLeftInverse076 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![0, 0, -2, 3]
  · obtain ⟨q, hq'⟩ := (blockSupport076 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables077 : Fin 1 → Fin 26 × Fin 26 :=
  ![(10, 15)]
private def blockConstraints077 : Fin 1 → DerivationConstraint :=
  ![.entry 1 0 15]
private def blockA077 : Matrix (Fin 1) (Fin 1) (ZMod 2) :=
  ![![1]]
private def blockB077 : Matrix (Fin 1) (Fin 1) (ZMod 2) :=
  ![![1]]

private theorem blockLeftInverse077 : blockB077 * blockA077 = 1 := by
  decide +kernel

private theorem blockSupport077 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![0, 0, -2, 4] k) ↔ ∃ q, blockVariables077 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 77, a nonroot degree with 1 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock077 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 0, -2, 4] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 1) : (blockConstraints077 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 1 → R := fun q => X (blockVariables077 q).1 (blockVariables077 q).2
  have hx : blockA077.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA077 r i) * x i = 0
    have h := hc r
    fin_cases r; simp [blockA077, blockConstraints077, DerivationConstraint.evaluate, x,
        blockVariables077, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA077 blockB077
    blockLeftInverse077 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![0, 0, -2, 4]
  · obtain ⟨q, hq'⟩ := (blockSupport077 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables078 : Fin 2 → Fin 26 × Fin 26 :=
  ![(24, 0), (25, 1)]
private def blockConstraints078 : Fin 2 → DerivationConstraint :=
  ![.entry 0 12 1, .entry 0 13 1]
private def blockA078 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 1], ![1, 0]]
private def blockB078 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 1]]

private theorem blockLeftInverse078 : blockB078 * blockA078 = 1 := by
  decide +kernel

private theorem blockSupport078 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![0, 0, -1, 0] k) ↔ ∃ q, blockVariables078 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 78, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock078 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 0, -1, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints078 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables078 q).1 (blockVariables078 q).2
  have hx : blockA078.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA078 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA078, blockConstraints078, DerivationConstraint.evaluate, x,
        blockVariables078, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA078 blockB078
    blockLeftInverse078 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![0, 0, -1, 0]
  · obtain ⟨q, hq'⟩ := (blockSupport078 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables079 : Fin 12 → Fin 26 × Fin 26 :=
  ![(10, 0), (12, 1), (13, 1), (14, 2), (16, 3), (18, 4), (21, 7), (22, 9), (23, 11), (24, 12),
      (24, 13), (25, 15)]
private def blockConstraints079 : Fin 12 → DerivationConstraint :=
  ![.entry 0 0 1, .entry 0 5 7, .entry 0 6 9, .entry 0 8 11, .entry 0 10 12, .entry 0 10 13,
      .entry 0 12 15, .entry 0 14 17, .entry 0 16 19, .entry 0 18 20, .entry 1 2 2, .ideal 24]
private def blockA079 : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ![![1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
      ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
      ![1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
      ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      ![0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
private def blockB079 : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1],
      ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1],
      ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1],
      ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1],
      ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1]]

private theorem blockLeftInverse079 : blockB079 * blockA079 = 1 := by
  decide +kernel

private theorem blockSupport079 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![0, 0, -1, 1] k) ↔ ∃ q, blockVariables079 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 79, a root degree with 12 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock079 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 0, -1, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 12) : (blockConstraints079 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 12 → R := fun q => X (blockVariables079 q).1 (blockVariables079 q).2
  have hx : blockA079.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA079 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA079, blockConstraints079, DerivationConstraint.evaluate, x,
        blockVariables079, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA079 blockB079
    blockLeftInverse079 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![0, 0, -1, 1]
  · obtain ⟨q, hq'⟩ := (blockSupport079 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables080 : Fin 12 → Fin 26 × Fin 26 :=
  ![(0, 1), (5, 7), (6, 9), (8, 11), (10, 12), (10, 13), (12, 15), (13, 15), (14, 17),
      (16, 19), (18, 20), (24, 25)]
private def blockConstraints080 : Fin 12 → DerivationConstraint :=
  ![.entry 0 0 15, .entry 0 10 25, .entry 1 0 12, .entry 1 0 13, .entry 1 1 15, .entry 1 2 17,
      .entry 1 3 19, .entry 1 4 20, .entry 1 5 21, .entry 1 6 22, .entry 1 8 23, .ideal 10]
private def blockA080 : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ![![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1],
      ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      ![1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
      ![1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
      ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
private def blockB080 : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
      ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1],
      ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1], ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

private theorem blockLeftInverse080 : blockB080 * blockA080 = 1 := by
  decide +kernel

private theorem blockSupport080 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![0, 0, -1, 2] k) ↔ ∃ q, blockVariables080 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 80, a root degree with 12 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock080 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 0, -1, 2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 12) : (blockConstraints080 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 12 → R := fun q => X (blockVariables080 q).1 (blockVariables080 q).2
  have hx : blockA080.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA080 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA080, blockConstraints080, DerivationConstraint.evaluate, x,
        blockVariables080, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA080 blockB080
    blockLeftInverse080 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![0, 0, -1, 2]
  · obtain ⟨q, hq'⟩ := (blockSupport080 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables081 : Fin 2 → Fin 26 × Fin 26 :=
  ![(0, 15), (10, 25)]
private def blockConstraints081 : Fin 2 → DerivationConstraint :=
  ![.entry 1 0 25, .entry 7 0 20]
private def blockA081 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 1], ![1, 0]]
private def blockB081 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 1]]

private theorem blockLeftInverse081 : blockB081 * blockA081 = 1 := by
  decide +kernel

private theorem blockSupport081 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![0, 0, -1, 3] k) ↔ ∃ q, blockVariables081 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 81, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock081 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 0, -1, 3] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints081 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables081 q).1 (blockVariables081 q).2
  have hx : blockA081.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA081 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA081, blockConstraints081, DerivationConstraint.evaluate, x,
        blockVariables081, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA081 blockB081
    blockLeftInverse081 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![0, 0, -1, 3]
  · obtain ⟨q, hq'⟩ := (blockSupport081 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables082 : Fin 1 → Fin 26 × Fin 26 :=
  ![(25, 0)]
private def blockConstraints082 : Fin 1 → DerivationConstraint :=
  ![.entry 0 15 1]
private def blockA082 : Matrix (Fin 1) (Fin 1) (ZMod 2) :=
  ![![1]]
private def blockB082 : Matrix (Fin 1) (Fin 1) (ZMod 2) :=
  ![![1]]

private theorem blockLeftInverse082 : blockB082 * blockA082 = 1 := by
  decide +kernel

private theorem blockSupport082 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![0, 0, 0, -2] k) ↔ ∃ q, blockVariables082 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 82, a nonroot degree with 1 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock082 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 0, 0, -2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 1) : (blockConstraints082 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 1 → R := fun q => X (blockVariables082 q).1 (blockVariables082 q).2
  have hx : blockA082.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA082 r i) * x i = 0
    have h := hc r
    fin_cases r; simp [blockA082, blockConstraints082, DerivationConstraint.evaluate, x,
        blockVariables082, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA082 blockB082
    blockLeftInverse082 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![0, 0, 0, -2]
  · obtain ⟨q, hq'⟩ := (blockSupport082 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables083 : Fin 12 → Fin 26 × Fin 26 :=
  ![(12, 0), (13, 0), (15, 1), (17, 2), (19, 3), (20, 4), (21, 5), (22, 6), (23, 8), (24, 10),
      (25, 12), (25, 13)]
private def blockConstraints083 : Fin 12 → DerivationConstraint :=
  ![.entry 0 1 1, .entry 0 2 2, .entry 0 3 3, .entry 0 4 4, .entry 0 5 5, .entry 0 6 6,
      .entry 0 7 7, .entry 0 8 8, .entry 0 10 10, .entry 0 12 12, .entry 0 12 13, .ideal 25]
private def blockA083 : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ![![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      ![1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
      ![1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
      ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
private def blockB083 : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
      ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
      ![0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1],
      ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]]

private theorem blockLeftInverse083 : blockB083 * blockA083 = 1 := by
  decide +kernel

private theorem blockSupport083 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![0, 0, 0, -1] k) ↔ ∃ q, blockVariables083 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 83, a root degree with 12 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock083 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 0, 0, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 12) : (blockConstraints083 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 12 → R := fun q => X (blockVariables083 q).1 (blockVariables083 q).2
  have hx : blockA083.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA083 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA083, blockConstraints083, DerivationConstraint.evaluate, x,
        blockVariables083, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA083 blockB083
    blockLeftInverse083 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![0, 0, 0, -1]
  · obtain ⟨q, hq'⟩ := (blockSupport083 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd


end TauCeti.F4ShortRoot
