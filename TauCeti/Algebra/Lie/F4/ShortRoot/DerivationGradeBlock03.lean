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

private def blockVariables042 : Fin 12 → Fin 26 × Fin 26 :=
  ![(6, 0), (9, 1), (12, 3), (13, 3), (14, 5), (17, 7), (18, 8), (20, 11), (22, 12), (22, 13),
      (24, 16), (25, 19)]
private def blockConstraints042 : Fin 12 → DerivationConstraint :=
  ![.entry 0 0 3, .entry 0 2 7, .entry 0 4 11, .entry 0 6 12, .entry 0 6 13, .entry 0 9 15,
      .entry 0 10 16, .entry 0 12 19, .entry 0 14 21, .entry 0 18 23, .entry 1 1 3, .ideal 22]
private def blockA042 : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ![![1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
      ![0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
private def blockB042 : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1],
      ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1], ![1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 1]]

private theorem blockLeftInverse042 : blockB042 * blockA042 = 1 := by
  decide +kernel

private theorem blockSupport042 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-1, 1, -1, 0] k) ↔ ∃ q, blockVariables042 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 42, a root degree with 12 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock042 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 1, -1, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 12) : (blockConstraints042 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 12 → R := fun q => X (blockVariables042 q).1 (blockVariables042 q).2
  have hx : blockA042.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA042 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA042, blockConstraints042, DerivationConstraint.evaluate, x,
        blockVariables042, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA042 blockB042
    blockLeftInverse042 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-1, 1, -1, 0]
  · obtain ⟨q, hq'⟩ := (blockSupport042 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables043 : Fin 12 → Fin 26 × Fin 26 :=
  ![(0, 3), (2, 7), (4, 11), (6, 12), (6, 13), (9, 15), (10, 16), (12, 19), (13, 19), (14, 21),
      (18, 23), (22, 25)]
private def blockConstraints043 : Fin 12 → DerivationConstraint :=
  ![.entry 0 0 19, .entry 0 6 25, .entry 1 0 16, .entry 1 1 19, .entry 1 2 21, .entry 1 4 23,
      .entry 1 6 24, .entry 1 9 25, .entry 2 2 19, .entry 2 6 23, .entry 3 0 12, .ideal 6]
private def blockA043 : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ![![1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
      ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0],
      ![0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0],
      ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1],
      ![0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0],
      ![1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
private def blockB043 : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1],
      ![0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
      ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1], ![0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1],
      ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
      ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1],
      ![0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]]

private theorem blockLeftInverse043 : blockB043 * blockA043 = 1 := by
  decide +kernel

private theorem blockSupport043 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-1, 1, -1, 1] k) ↔ ∃ q, blockVariables043 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 43, a root degree with 12 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock043 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 1, -1, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 12) : (blockConstraints043 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 12 → R := fun q => X (blockVariables043 q).1 (blockVariables043 q).2
  have hx : blockA043.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA043 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA043, blockConstraints043, DerivationConstraint.evaluate, x,
        blockVariables043, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA043 blockB043
    blockLeftInverse043 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-1, 1, -1, 1]
  · obtain ⟨q, hq'⟩ := (blockSupport043 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables044 : Fin 2 → Fin 26 × Fin 26 :=
  ![(0, 19), (6, 25)]
private def blockConstraints044 : Fin 2 → DerivationConstraint :=
  ![.entry 3 0 25, .entry 7 0 23]
private def blockA044 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 1], ![1, 0]]
private def blockB044 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 1]]

private theorem blockLeftInverse044 : blockB044 * blockA044 = 1 := by
  decide +kernel

private theorem blockSupport044 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-1, 1, -1, 2] k) ↔ ∃ q, blockVariables044 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 44, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock044 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 1, -1, 2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints044 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables044 q).1 (blockVariables044 q).2
  have hx : blockA044.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA044 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA044, blockConstraints044, DerivationConstraint.evaluate, x,
        blockVariables044, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA044 blockB044
    blockLeftInverse044 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-1, 1, -1, 2]
  · obtain ⟨q, hq'⟩ := (blockSupport044 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables045 : Fin 6 → Fin 26 × Fin 26 :=
  ![(9, 0), (15, 3), (17, 5), (20, 8), (22, 10), (25, 16)]
private def blockConstraints045 : Fin 6 → DerivationConstraint :=
  ![.entry 0 1 3, .entry 0 2 5, .entry 0 4 8, .entry 0 6 10, .entry 0 12 16, .quotient 20]
private def blockA045 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ![![1, 1, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0],
      ![1, 0, 0, 0, 0, 1], ![1, 0, 0, 0, 0, 0]]
private def blockB045 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 1], ![1, 0, 0, 0, 0, 1], ![0, 1, 0, 0, 0, 1], ![0, 0, 1, 0, 0, 1],
      ![0, 0, 0, 1, 0, 1], ![0, 0, 0, 0, 1, 1]]

private theorem blockLeftInverse045 : blockB045 * blockA045 = 1 := by
  decide +kernel

private theorem blockSupport045 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-1, 1, 0, -2] k) ↔ ∃ q, blockVariables045 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 45, a root degree with 6 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock045 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 1, 0, -2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 6) : (blockConstraints045 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 6 → R := fun q => X (blockVariables045 q).1 (blockVariables045 q).2
  have hx : blockA045.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA045 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA045, blockConstraints045, DerivationConstraint.evaluate, x,
        blockVariables045, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA045 blockB045
    blockLeftInverse045 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-1, 1, 0, -2]
  · obtain ⟨q, hq'⟩ := (blockSupport045 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables046 : Fin 12 → Fin 26 × Fin 26 :=
  ![(1, 3), (2, 5), (4, 8), (6, 10), (9, 12), (9, 13), (12, 16), (13, 16), (15, 19), (17, 21),
      (20, 23), (22, 24)]
private def blockConstraints046 : Fin 12 → DerivationConstraint :=
  ![.entry 0 0 16, .entry 0 1 19, .entry 0 2 21, .entry 0 4 23, .entry 0 6 24, .entry 0 9 25,
      .entry 1 1 16, .entry 1 9 24, .entry 2 2 16, .entry 2 9 23, .entry 3 0 10, .ideal 9]
private def blockA046 : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
      ![0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0],
      ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
      ![1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1],
      ![0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0],
      ![1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
private def blockB046 : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1],
      ![0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
      ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1],
      ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1],
      ![0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1]]

private theorem blockLeftInverse046 : blockB046 * blockA046 = 1 := by
  decide +kernel

private theorem blockSupport046 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-1, 1, 0, -1] k) ↔ ∃ q, blockVariables046 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 46, a root degree with 12 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock046 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 1, 0, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 12) : (blockConstraints046 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 12 → R := fun q => X (blockVariables046 q).1 (blockVariables046 q).2
  have hx : blockA046.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA046 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA046, blockConstraints046, DerivationConstraint.evaluate, x,
        blockVariables046, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA046 blockB046
    blockLeftInverse046 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-1, 1, 0, -1]
  · obtain ⟨q, hq'⟩ := (blockSupport046 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables047 : Fin 6 → Fin 26 × Fin 26 :=
  ![(0, 16), (1, 19), (2, 21), (4, 23), (6, 24), (9, 25)]
private def blockConstraints047 : Fin 6 → DerivationConstraint :=
  ![.entry 3 0 24, .entry 3 1 25, .entry 5 0 23, .entry 5 2 25, .entry 7 1 23, .quotient 1]
private def blockA047 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ![![1, 0, 0, 0, 1, 0], ![0, 1, 0, 0, 0, 1], ![1, 0, 0, 1, 0, 0], ![0, 0, 1, 0, 0, 1],
      ![0, 1, 0, 1, 0, 0], ![1, 0, 0, 0, 0, 0]]
private def blockB047 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 1], ![0, 0, 1, 0, 1, 1], ![0, 1, 1, 1, 1, 1], ![0, 0, 1, 0, 0, 1],
      ![1, 0, 0, 0, 0, 1], ![0, 1, 1, 0, 1, 1]]

private theorem blockLeftInverse047 : blockB047 * blockA047 = 1 := by
  decide +kernel

private theorem blockSupport047 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-1, 1, 0, 0] k) ↔ ∃ q, blockVariables047 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 47, a root degree with 6 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock047 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 1, 0, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 6) : (blockConstraints047 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 6 → R := fun q => X (blockVariables047 q).1 (blockVariables047 q).2
  have hx : blockA047.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA047 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA047, blockConstraints047, DerivationConstraint.evaluate, x,
        blockVariables047, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA047 blockB047
    blockLeftInverse047 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-1, 1, 0, 0]
  · obtain ⟨q, hq'⟩ := (blockSupport047 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables048 : Fin 2 → Fin 26 × Fin 26 :=
  ![(9, 10), (15, 16)]
private def blockConstraints048 : Fin 2 → DerivationConstraint :=
  ![.entry 0 1 16, .entry 0 9 24]
private def blockA048 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]
private def blockB048 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]

private theorem blockLeftInverse048 : blockB048 * blockA048 = 1 := by
  decide +kernel

private theorem blockSupport048 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-1, 1, 1, -3] k) ↔ ∃ q, blockVariables048 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 48, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock048 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 1, 1, -3] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints048 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables048 q).1 (blockVariables048 q).2
  have hx : blockA048.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA048 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA048, blockConstraints048, DerivationConstraint.evaluate, x,
        blockVariables048, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA048 blockB048
    blockLeftInverse048 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-1, 1, 1, -3]
  · obtain ⟨q, hq'⟩ := (blockSupport048 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables049 : Fin 2 → Fin 26 × Fin 26 :=
  ![(1, 16), (9, 24)]
private def blockConstraints049 : Fin 2 → DerivationConstraint :=
  ![.entry 3 1 24, .entry 5 1 23]
private def blockA049 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 1], ![1, 0]]
private def blockB049 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 1]]

private theorem blockLeftInverse049 : blockB049 * blockA049 = 1 := by
  decide +kernel

private theorem blockSupport049 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-1, 1, 1, -2] k) ↔ ∃ q, blockVariables049 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 49, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock049 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 1, 1, -2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints049 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables049 q).1 (blockVariables049 q).2
  have hx : blockA049.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA049 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA049, blockConstraints049, DerivationConstraint.evaluate, x,
        blockVariables049, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA049 blockB049
    blockLeftInverse049 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-1, 1, 1, -2]
  · obtain ⟨q, hq'⟩ := (blockSupport049 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables050 : Fin 2 → Fin 26 × Fin 26 :=
  ![(14, 3), (22, 11)]
private def blockConstraints050 : Fin 2 → DerivationConstraint :=
  ![.entry 0 6 11, .entry 0 14 19]
private def blockA050 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]
private def blockB050 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]

private theorem blockLeftInverse050 : blockB050 * blockA050 = 1 := by
  decide +kernel

private theorem blockSupport050 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-1, 2, -3, 1] k) ↔ ∃ q, blockVariables050 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 50, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock050 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 2, -3, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints050 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables050 q).1 (blockVariables050 q).2
  have hx : blockA050.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA050 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA050, blockConstraints050, DerivationConstraint.evaluate, x,
        blockVariables050, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA050 blockB050
    blockLeftInverse050 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-1, 2, -3, 1]
  · obtain ⟨q, hq'⟩ := (blockSupport050 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables051 : Fin 2 → Fin 26 × Fin 26 :=
  ![(6, 11), (14, 19)]
private def blockConstraints051 : Fin 2 → DerivationConstraint :=
  ![.entry 1 2 19, .entry 1 6 23]
private def blockA051 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]
private def blockB051 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]

private theorem blockLeftInverse051 : blockB051 * blockA051 = 1 := by
  decide +kernel

private theorem blockSupport051 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-1, 2, -3, 2] k) ↔ ∃ q, blockVariables051 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 51, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock051 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 2, -3, 2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints051 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables051 q).1 (blockVariables051 q).2
  have hx : blockA051.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA051 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA051, blockConstraints051, DerivationConstraint.evaluate, x,
        blockVariables051, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA051 blockB051
    blockLeftInverse051 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-1, 2, -3, 2]
  · obtain ⟨q, hq'⟩ := (blockSupport051 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables052 : Fin 2 → Fin 26 × Fin 26 :=
  ![(17, 3), (22, 8)]
private def blockConstraints052 : Fin 2 → DerivationConstraint :=
  ![.entry 0 2 3, .entry 0 6 8]
private def blockA052 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 0], ![0, 1]]
private def blockB052 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 0], ![0, 1]]

private theorem blockLeftInverse052 : blockB052 * blockA052 = 1 := by
  decide +kernel

private theorem blockSupport052 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-1, 2, -2, -1] k) ↔ ∃ q, blockVariables052 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 52, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock052 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 2, -2, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints052 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables052 q).1 (blockVariables052 q).2
  have hx : blockA052.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA052 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA052, blockConstraints052, DerivationConstraint.evaluate, x,
        blockVariables052, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA052 blockB052
    blockLeftInverse052 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-1, 2, -2, -1]
  · obtain ⟨q, hq'⟩ := (blockSupport052 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables053 : Fin 6 → Fin 26 × Fin 26 :=
  ![(2, 3), (6, 8), (9, 11), (14, 16), (17, 19), (22, 23)]
private def blockConstraints053 : Fin 6 → DerivationConstraint :=
  ![.entry 0 2 19, .entry 0 6 23, .entry 1 2 16, .entry 1 9 23, .entry 3 0 8, .quotient 11]
private def blockA053 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ![![1, 0, 0, 0, 1, 0], ![0, 1, 0, 0, 0, 1], ![1, 0, 0, 1, 0, 0], ![0, 0, 1, 0, 0, 1],
      ![1, 1, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0]]
private def blockB053 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 1], ![0, 1, 0, 1, 1, 1], ![0, 0, 1, 0, 0, 1],
      ![1, 0, 0, 0, 0, 1], ![0, 1, 0, 0, 1, 1]]

private theorem blockLeftInverse053 : blockB053 * blockA053 = 1 := by
  decide +kernel

private theorem blockSupport053 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-1, 2, -2, 0] k) ↔ ∃ q, blockVariables053 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 53, a root degree with 6 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock053 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 2, -2, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 6) : (blockConstraints053 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 6 → R := fun q => X (blockVariables053 q).1 (blockVariables053 q).2
  have hx : blockA053.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA053 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA053, blockConstraints053, DerivationConstraint.evaluate, x,
        blockVariables053, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA053 blockB053
    blockLeftInverse053 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-1, 2, -2, 0]
  · obtain ⟨q, hq'⟩ := (blockSupport053 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables054 : Fin 2 → Fin 26 × Fin 26 :=
  ![(2, 19), (6, 23)]
private def blockConstraints054 : Fin 2 → DerivationConstraint :=
  ![.entry 3 0 23, .entry 3 2 25]
private def blockA054 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]
private def blockB054 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]

private theorem blockLeftInverse054 : blockB054 * blockA054 = 1 := by
  decide +kernel

private theorem blockSupport054 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-1, 2, -2, 1] k) ↔ ∃ q, blockVariables054 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 54, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock054 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 2, -2, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints054 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables054 q).1 (blockVariables054 q).2
  have hx : blockA054.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA054 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA054, blockConstraints054, DerivationConstraint.evaluate, x,
        blockVariables054, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA054 blockB054
    blockLeftInverse054 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-1, 2, -2, 1]
  · obtain ⟨q, hq'⟩ := (blockSupport054 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables055 : Fin 2 → Fin 26 × Fin 26 :=
  ![(9, 8), (17, 16)]
private def blockConstraints055 : Fin 2 → DerivationConstraint :=
  ![.entry 0 2 16, .entry 0 9 23]
private def blockA055 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]
private def blockB055 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]

private theorem blockLeftInverse055 : blockB055 * blockA055 = 1 := by
  decide +kernel

private theorem blockSupport055 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-1, 2, -1, -2] k) ↔ ∃ q, blockVariables055 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 55, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock055 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 2, -1, -2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints055 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables055 q).1 (blockVariables055 q).2
  have hx : blockA055.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA055 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA055, blockConstraints055, DerivationConstraint.evaluate, x,
        blockVariables055, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA055 blockB055
    blockLeftInverse055 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-1, 2, -1, -2]
  · obtain ⟨q, hq'⟩ := (blockSupport055 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd


end TauCeti.F4ShortRoot
