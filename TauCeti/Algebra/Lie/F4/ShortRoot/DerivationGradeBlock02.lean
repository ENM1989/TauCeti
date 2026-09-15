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

private def blockVariables028 : Fin 6 → Fin 26 × Fin 26 :=
  ![(18, 0), (20, 1), (22, 2), (23, 3), (24, 5), (25, 7)]
private def blockConstraints028 : Fin 6 → DerivationConstraint :=
  ![.entry 0 4 1, .entry 0 6 2, .entry 0 8 3, .entry 0 10 5, .entry 0 12 7, .quotient 25]
private def blockA028 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ![![1, 1, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0],
      ![1, 0, 0, 0, 0, 1], ![1, 0, 0, 0, 0, 0]]
private def blockB028 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 1], ![1, 0, 0, 0, 0, 1], ![0, 1, 0, 0, 0, 1], ![0, 0, 1, 0, 0, 1],
      ![0, 0, 0, 1, 0, 1], ![0, 0, 0, 0, 1, 1]]

private theorem blockLeftInverse028 : blockB028 * blockA028 = 1 := by
  decide +kernel

private theorem blockSupport028 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-1, 0, 0, 0] k) ↔ ∃ q, blockVariables028 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 28, a root degree with 6 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock028 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 0, 0, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 6) : (blockConstraints028 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 6 → R := fun q => X (blockVariables028 q).1 (blockVariables028 q).2
  have hx : blockA028.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA028 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA028, blockConstraints028, DerivationConstraint.evaluate, x,
        blockVariables028, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA028 blockB028
    blockLeftInverse028 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-1, 0, 0, 0]
  · obtain ⟨q, hq'⟩ := (blockSupport028 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables029 : Fin 12 → Fin 26 × Fin 26 :=
  ![(4, 1), (6, 2), (8, 3), (10, 5), (12, 7), (13, 7), (18, 12), (18, 13), (20, 15), (22, 17),
      (23, 19), (24, 21)]
private def blockConstraints029 : Fin 12 → DerivationConstraint :=
  ![.entry 0 0 7, .entry 0 4 15, .entry 0 6 17, .entry 0 8 19, .entry 0 10 21, .entry 0 18 25,
      .entry 1 0 5, .entry 1 1 7, .entry 1 4 13, .entry 1 6 14, .entry 1 8 16, .ideal 18]
private def blockA029 : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
      ![0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0],
      ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
      ![1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0],
      ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
private def blockB029 : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1],
      ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1],
      ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1],
      ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1], ![0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1]]

private theorem blockLeftInverse029 : blockB029 * blockA029 = 1 := by
  decide +kernel

private theorem blockSupport029 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-1, 0, 0, 1] k) ↔ ∃ q, blockVariables029 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 29, a root degree with 12 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock029 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 0, 0, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 12) : (blockConstraints029 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 12 → R := fun q => X (blockVariables029 q).1 (blockVariables029 q).2
  have hx : blockA029.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA029 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA029, blockConstraints029, DerivationConstraint.evaluate, x,
        blockVariables029, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA029 blockB029
    blockLeftInverse029 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-1, 0, 0, 1]
  · obtain ⟨q, hq'⟩ := (blockSupport029 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables030 : Fin 6 → Fin 26 × Fin 26 :=
  ![(0, 7), (4, 15), (6, 17), (8, 19), (10, 21), (18, 25)]
private def blockConstraints030 : Fin 6 → DerivationConstraint :=
  ![.entry 1 0 21, .entry 1 4 25, .entry 2 0 19, .entry 2 6 25, .entry 3 0 17, .quotient 7]
private def blockA030 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ![![1, 0, 0, 0, 1, 0], ![0, 1, 0, 0, 0, 1], ![1, 0, 0, 1, 0, 0], ![0, 0, 1, 0, 0, 1],
      ![1, 0, 1, 0, 0, 0], ![1, 0, 0, 0, 0, 0]]
private def blockB030 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 1], ![0, 1, 0, 1, 1, 1], ![0, 0, 0, 0, 1, 1], ![0, 0, 1, 0, 0, 1],
      ![1, 0, 0, 0, 0, 1], ![0, 0, 0, 1, 1, 1]]

private theorem blockLeftInverse030 : blockB030 * blockA030 = 1 := by
  decide +kernel

private theorem blockSupport030 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-1, 0, 0, 2] k) ↔ ∃ q, blockVariables030 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 30, a root degree with 6 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock030 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 0, 0, 2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 6) : (blockConstraints030 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 6 → R := fun q => X (blockVariables030 q).1 (blockVariables030 q).2
  have hx : blockA030.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA030 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA030, blockConstraints030, DerivationConstraint.evaluate, x,
        blockVariables030, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA030 blockB030
    blockLeftInverse030 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-1, 0, 0, 2]
  · obtain ⟨q, hq'⟩ := (blockSupport030 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables031 : Fin 2 → Fin 26 × Fin 26 :=
  ![(20, 0), (25, 5)]
private def blockConstraints031 : Fin 2 → DerivationConstraint :=
  ![.entry 0 9 2, .entry 0 12 5]
private def blockA031 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 0], ![1, 1]]
private def blockB031 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 0], ![1, 1]]

private theorem blockLeftInverse031 : blockB031 * blockA031 = 1 := by
  decide +kernel

private theorem blockSupport031 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-1, 0, 1, -2] k) ↔ ∃ q, blockVariables031 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 31, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock031 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 0, 1, -2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints031 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables031 q).1 (blockVariables031 q).2
  have hx : blockA031.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA031 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA031, blockConstraints031, DerivationConstraint.evaluate, x,
        blockVariables031, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA031 blockB031
    blockLeftInverse031 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-1, 0, 1, -2]
  · obtain ⟨q, hq'⟩ := (blockSupport031 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables032 : Fin 12 → Fin 26 × Fin 26 :=
  ![(4, 0), (9, 2), (11, 3), (12, 5), (13, 5), (15, 7), (18, 10), (20, 12), (20, 13), (22, 14),
      (23, 16), (25, 21)]
private def blockConstraints032 : Fin 12 → DerivationConstraint :=
  ![.entry 0 0 5, .entry 0 1 7, .entry 0 4 12, .entry 0 4 13, .entry 0 6 14, .entry 0 8 16,
      .entry 0 9 17, .entry 0 11 19, .entry 0 12 21, .entry 0 18 24, .entry 1 1 5, .ideal 20]
private def blockA032 : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ![![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
      ![1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
      ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
      ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
private def blockB032 : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1],
      ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
      ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1],
      ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1], ![1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1]]

private theorem blockLeftInverse032 : blockB032 * blockA032 = 1 := by
  decide +kernel

private theorem blockSupport032 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-1, 0, 1, -1] k) ↔ ∃ q, blockVariables032 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 32, a root degree with 12 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock032 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 0, 1, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 12) : (blockConstraints032 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 12 → R := fun q => X (blockVariables032 q).1 (blockVariables032 q).2
  have hx : blockA032.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA032 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA032, blockConstraints032, DerivationConstraint.evaluate, x,
        blockVariables032, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA032 blockB032
    blockLeftInverse032 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-1, 0, 1, -1]
  · obtain ⟨q, hq'⟩ := (blockSupport032 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables033 : Fin 12 → Fin 26 × Fin 26 :=
  ![(0, 5), (1, 7), (4, 12), (4, 13), (6, 14), (8, 16), (9, 17), (11, 19), (12, 21), (13, 21),
      (18, 24), (20, 25)]
private def blockConstraints033 : Fin 12 → DerivationConstraint :=
  ![.entry 0 0 21, .entry 0 4 25, .entry 1 1 21, .entry 1 4 24, .entry 2 0 16, .entry 2 1 19,
      .entry 2 2 21, .entry 2 4 23, .entry 2 6 24, .entry 2 9 25, .entry 3 0 14, .ideal 4]
private def blockA033 : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      ![0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0], ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0],
      ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1],
      ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
private def blockB033 : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1],
      ![0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 1], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1],
      ![0, 1, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1], ![1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1],
      ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1], ![0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 1, 1]]

private theorem blockLeftInverse033 : blockB033 * blockA033 = 1 := by
  decide +kernel

private theorem blockSupport033 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-1, 0, 1, 0] k) ↔ ∃ q, blockVariables033 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 33, a root degree with 12 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock033 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 0, 1, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 12) : (blockConstraints033 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 12 → R := fun q => X (blockVariables033 q).1 (blockVariables033 q).2
  have hx : blockA033.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA033 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA033, blockConstraints033, DerivationConstraint.evaluate, x,
        blockVariables033, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA033 blockB033
    blockLeftInverse033 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-1, 0, 1, 0]
  · obtain ⟨q, hq'⟩ := (blockSupport033 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables034 : Fin 2 → Fin 26 × Fin 26 :=
  ![(0, 21), (4, 25)]
private def blockConstraints034 : Fin 2 → DerivationConstraint :=
  ![.entry 5 0 25, .entry 7 0 24]
private def blockA034 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 1], ![1, 0]]
private def blockB034 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 1]]

private theorem blockLeftInverse034 : blockB034 * blockA034 = 1 := by
  decide +kernel

private theorem blockSupport034 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-1, 0, 1, 1] k) ↔ ∃ q, blockVariables034 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 34, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock034 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 0, 1, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints034 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables034 q).1 (blockVariables034 q).2
  have hx : blockA034.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA034 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA034, blockConstraints034, DerivationConstraint.evaluate, x,
        blockVariables034, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA034 blockB034
    blockLeftInverse034 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-1, 0, 1, 1]
  · obtain ⟨q, hq'⟩ := (blockSupport034 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables035 : Fin 2 → Fin 26 × Fin 26 :=
  ![(15, 5), (20, 10)]
private def blockConstraints035 : Fin 2 → DerivationConstraint :=
  ![.entry 0 1 5, .entry 0 4 10]
private def blockA035 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 0], ![0, 1]]
private def blockB035 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 0], ![0, 1]]

private theorem blockLeftInverse035 : blockB035 * blockA035 = 1 := by
  decide +kernel

private theorem blockSupport035 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-1, 0, 2, -3] k) ↔ ∃ q, blockVariables035 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 35, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock035 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 0, 2, -3] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints035 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables035 q).1 (blockVariables035 q).2
  have hx : blockA035.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA035 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA035, blockConstraints035, DerivationConstraint.evaluate, x,
        blockVariables035, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA035 blockB035
    blockLeftInverse035 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-1, 0, 2, -3]
  · obtain ⟨q, hq'⟩ := (blockSupport035 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables036 : Fin 6 → Fin 26 × Fin 26 :=
  ![(1, 5), (4, 10), (9, 14), (11, 16), (15, 21), (20, 24)]
private def blockConstraints036 : Fin 6 → DerivationConstraint :=
  ![.entry 0 1 21, .entry 0 4 24, .entry 2 1 16, .entry 2 9 24, .entry 3 1 14, .quotient 9]
private def blockA036 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ![![1, 0, 0, 0, 1, 0], ![0, 1, 0, 0, 0, 1], ![1, 0, 0, 1, 0, 0], ![0, 0, 1, 0, 0, 1],
      ![1, 0, 1, 0, 0, 0], ![1, 0, 0, 0, 0, 0]]
private def blockB036 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 1], ![0, 1, 0, 1, 1, 1], ![0, 0, 0, 0, 1, 1], ![0, 0, 1, 0, 0, 1],
      ![1, 0, 0, 0, 0, 1], ![0, 0, 0, 1, 1, 1]]

private theorem blockLeftInverse036 : blockB036 * blockA036 = 1 := by
  decide +kernel

private theorem blockSupport036 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-1, 0, 2, -2] k) ↔ ∃ q, blockVariables036 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 36, a root degree with 6 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock036 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 0, 2, -2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 6) : (blockConstraints036 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 6 → R := fun q => X (blockVariables036 q).1 (blockVariables036 q).2
  have hx : blockA036.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA036 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA036, blockConstraints036, DerivationConstraint.evaluate, x,
        blockVariables036, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA036 blockB036
    blockLeftInverse036 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-1, 0, 2, -2]
  · obtain ⟨q, hq'⟩ := (blockSupport036 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables037 : Fin 2 → Fin 26 × Fin 26 :=
  ![(1, 21), (4, 24)]
private def blockConstraints037 : Fin 2 → DerivationConstraint :=
  ![.entry 5 0 24, .entry 5 1 25]
private def blockA037 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]
private def blockB037 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]

private theorem blockLeftInverse037 : blockB037 * blockA037 = 1 := by
  decide +kernel

private theorem blockSupport037 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-1, 0, 2, -1] k) ↔ ∃ q, blockVariables037 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 37, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock037 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 0, 2, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints037 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables037 q).1 (blockVariables037 q).2
  have hx : blockA037.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA037 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA037, blockConstraints037, DerivationConstraint.evaluate, x,
        blockVariables037, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA037 blockB037
    blockLeftInverse037 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-1, 0, 2, -1]
  · obtain ⟨q, hq'⟩ := (blockSupport037 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables038 : Fin 2 → Fin 26 × Fin 26 :=
  ![(22, 1), (24, 3)]
private def blockConstraints038 : Fin 2 → DerivationConstraint :=
  ![.entry 0 6 1, .entry 0 10 3]
private def blockA038 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 0], ![0, 1]]
private def blockB038 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 0], ![0, 1]]

private theorem blockLeftInverse038 : blockB038 * blockA038 = 1 := by
  decide +kernel

private theorem blockSupport038 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-1, 1, -2, 1] k) ↔ ∃ q, blockVariables038 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 38, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock038 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 1, -2, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints038 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables038 q).1 (blockVariables038 q).2
  have hx : blockA038.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA038 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA038, blockConstraints038, DerivationConstraint.evaluate, x,
        blockVariables038, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA038 blockB038
    blockLeftInverse038 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-1, 1, -2, 1]
  · obtain ⟨q, hq'⟩ := (blockSupport038 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables039 : Fin 6 → Fin 26 × Fin 26 :=
  ![(6, 1), (10, 3), (14, 7), (18, 11), (22, 15), (24, 19)]
private def blockConstraints039 : Fin 6 → DerivationConstraint :=
  ![.entry 0 6 15, .entry 0 10 19, .entry 1 0 3, .entry 1 2 7, .entry 1 4 11, .quotient 19]
private def blockA039 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ![![1, 0, 0, 0, 1, 0], ![0, 1, 0, 0, 0, 1], ![1, 1, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0],
      ![1, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 0, 0]]
private def blockB039 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 1], ![0, 0, 1, 0, 0, 1], ![0, 0, 0, 1, 0, 1], ![0, 0, 0, 0, 1, 1],
      ![1, 0, 0, 0, 0, 1], ![0, 1, 1, 0, 0, 1]]

private theorem blockLeftInverse039 : blockB039 * blockA039 = 1 := by
  decide +kernel

private theorem blockSupport039 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-1, 1, -2, 2] k) ↔ ∃ q, blockVariables039 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 39, a root degree with 6 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock039 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 1, -2, 2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 6) : (blockConstraints039 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 6 → R := fun q => X (blockVariables039 q).1 (blockVariables039 q).2
  have hx : blockA039.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA039 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA039, blockConstraints039, DerivationConstraint.evaluate, x,
        blockVariables039, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA039 blockB039
    blockLeftInverse039 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-1, 1, -2, 2]
  · obtain ⟨q, hq'⟩ := (blockSupport039 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables040 : Fin 2 → Fin 26 × Fin 26 :=
  ![(6, 15), (10, 19)]
private def blockConstraints040 : Fin 2 → DerivationConstraint :=
  ![.entry 1 0 19, .entry 1 6 25]
private def blockA040 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]
private def blockB040 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]

private theorem blockLeftInverse040 : blockB040 * blockA040 = 1 := by
  decide +kernel

private theorem blockSupport040 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-1, 1, -2, 3] k) ↔ ∃ q, blockVariables040 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 40, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock040 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 1, -2, 3] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints040 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables040 q).1 (blockVariables040 q).2
  have hx : blockA040.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA040 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA040, blockConstraints040, DerivationConstraint.evaluate, x,
        blockVariables040, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA040 blockB040
    blockLeftInverse040 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-1, 1, -2, 3]
  · obtain ⟨q, hq'⟩ := (blockSupport040 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables041 : Fin 2 → Fin 26 × Fin 26 :=
  ![(22, 0), (25, 3)]
private def blockConstraints041 : Fin 2 → DerivationConstraint :=
  ![.entry 0 9 1, .entry 0 12 3]
private def blockA041 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 0], ![0, 1]]
private def blockB041 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 0], ![0, 1]]

private theorem blockLeftInverse041 : blockB041 * blockA041 = 1 := by
  decide +kernel

private theorem blockSupport041 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-1, 1, -1, -1] k) ↔ ∃ q, blockVariables041 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 41, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock041 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 1, -1, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints041 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables041 q).1 (blockVariables041 q).2
  have hx : blockA041.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA041 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA041, blockConstraints041, DerivationConstraint.evaluate, x,
        blockVariables041, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA041 blockB041
    blockLeftInverse041 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-1, 1, -1, -1]
  · obtain ⟨q, hq'⟩ := (blockSupport041 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd


end TauCeti.F4ShortRoot
