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

private def blockVariables112 : Fin 2 → Fin 26 × Fin 26 :=
  ![(8, 9), (16, 17)]
private def blockConstraints112 : Fin 2 → DerivationConstraint :=
  ![.entry 1 3 17, .entry 1 8 22]
private def blockA112 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]
private def blockB112 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]

private theorem blockLeftInverse112 : blockB112 * blockA112 = 1 := by
  decide +kernel

private theorem blockSupport112 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![1, -2, 1, 2] k) ↔ ∃ q, blockVariables112 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 112, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock112 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, -2, 1, 2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints112 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables112 q).1 (blockVariables112 q).2
  have hx : blockA112.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA112 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA112, blockConstraints112, DerivationConstraint.evaluate, x,
        blockVariables112, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA112 blockB112
    blockLeftInverse112 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![1, -2, 1, 2]
  · obtain ⟨q, hq'⟩ := (blockSupport112 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables113 : Fin 2 → Fin 26 × Fin 26 :=
  ![(19, 2), (23, 6)]
private def blockConstraints113 : Fin 2 → DerivationConstraint :=
  ![.entry 0 3 2, .entry 0 8 6]
private def blockA113 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 0], ![0, 1]]
private def blockB113 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 0], ![0, 1]]

private theorem blockLeftInverse113 : blockB113 * blockA113 = 1 := by
  decide +kernel

private theorem blockSupport113 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![1, -2, 2, -1] k) ↔ ∃ q, blockVariables113 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 113, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock113 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, -2, 2, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints113 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables113 q).1 (blockVariables113 q).2
  have hx : blockA113.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA113 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA113, blockConstraints113, DerivationConstraint.evaluate, x,
        blockVariables113, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA113 blockB113
    blockLeftInverse113 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![1, -2, 2, -1]
  · obtain ⟨q, hq'⟩ := (blockSupport113 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables114 : Fin 6 → Fin 26 × Fin 26 :=
  ![(3, 2), (8, 6), (11, 9), (16, 14), (19, 17), (23, 22)]
private def blockConstraints114 : Fin 6 → DerivationConstraint :=
  ![.entry 0 3 17, .entry 0 8 22, .entry 1 3 14, .entry 1 11 22, .entry 2 0 6, .quotient 14]
private def blockA114 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ![![1, 0, 0, 0, 1, 0], ![0, 1, 0, 0, 0, 1], ![1, 0, 0, 1, 0, 0], ![0, 0, 1, 0, 0, 1],
      ![1, 1, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0]]
private def blockB114 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 1], ![0, 1, 0, 1, 1, 1], ![0, 0, 1, 0, 0, 1],
      ![1, 0, 0, 0, 0, 1], ![0, 1, 0, 0, 1, 1]]

private theorem blockLeftInverse114 : blockB114 * blockA114 = 1 := by
  decide +kernel

private theorem blockSupport114 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![1, -2, 2, 0] k) ↔ ∃ q, blockVariables114 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 114, a root degree with 6 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock114 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, -2, 2, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 6) : (blockConstraints114 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 6 → R := fun q => X (blockVariables114 q).1 (blockVariables114 q).2
  have hx : blockA114.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA114 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA114, blockConstraints114, DerivationConstraint.evaluate, x,
        blockVariables114, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA114 blockB114
    blockLeftInverse114 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![1, -2, 2, 0]
  · obtain ⟨q, hq'⟩ := (blockSupport114 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables115 : Fin 2 → Fin 26 × Fin 26 :=
  ![(3, 17), (8, 22)]
private def blockConstraints115 : Fin 2 → DerivationConstraint :=
  ![.entry 2 0 22, .entry 2 3 25]
private def blockA115 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]
private def blockB115 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]

private theorem blockLeftInverse115 : blockB115 * blockA115 = 1 := by
  decide +kernel

private theorem blockSupport115 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![1, -2, 2, 1] k) ↔ ∃ q, blockVariables115 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 115, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock115 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, -2, 2, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints115 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables115 q).1 (blockVariables115 q).2
  have hx : blockA115.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA115 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA115, blockConstraints115, DerivationConstraint.evaluate, x,
        blockVariables115, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA115 blockB115
    blockLeftInverse115 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![1, -2, 2, 1]
  · obtain ⟨q, hq'⟩ := (blockSupport115 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables116 : Fin 2 → Fin 26 × Fin 26 :=
  ![(11, 6), (19, 14)]
private def blockConstraints116 : Fin 2 → DerivationConstraint :=
  ![.entry 0 3 14, .entry 0 11 22]
private def blockA116 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]
private def blockB116 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]

private theorem blockLeftInverse116 : blockB116 * blockA116 = 1 := by
  decide +kernel

private theorem blockSupport116 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![1, -2, 3, -2] k) ↔ ∃ q, blockVariables116 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 116, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock116 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, -2, 3, -2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints116 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables116 q).1 (blockVariables116 q).2
  have hx : blockA116.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA116 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA116, blockConstraints116, DerivationConstraint.evaluate, x,
        blockVariables116, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA116 blockB116
    blockLeftInverse116 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![1, -2, 3, -2]
  · obtain ⟨q, hq'⟩ := (blockSupport116 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables117 : Fin 2 → Fin 26 × Fin 26 :=
  ![(3, 14), (11, 22)]
private def blockConstraints117 : Fin 2 → DerivationConstraint :=
  ![.entry 2 1 22, .entry 2 3 24]
private def blockA117 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]
private def blockB117 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]

private theorem blockLeftInverse117 : blockB117 * blockA117 = 1 := by
  decide +kernel

private theorem blockSupport117 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![1, -2, 3, -1] k) ↔ ∃ q, blockVariables117 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 117, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock117 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, -2, 3, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints117 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables117 q).1 (blockVariables117 q).2
  have hx : blockA117.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA117 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA117, blockConstraints117, DerivationConstraint.evaluate, x,
        blockVariables117, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA117 blockB117
    blockLeftInverse117 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![1, -2, 3, -1]
  · obtain ⟨q, hq'⟩ := (blockSupport117 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables118 : Fin 2 → Fin 26 × Fin 26 :=
  ![(16, 1), (24, 9)]
private def blockConstraints118 : Fin 2 → DerivationConstraint :=
  ![.entry 0 10 9, .entry 0 16 15]
private def blockA118 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]
private def blockB118 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]

private theorem blockLeftInverse118 : blockB118 * blockA118 = 1 := by
  decide +kernel

private theorem blockSupport118 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![1, -1, -1, 2] k) ↔ ∃ q, blockVariables118 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 118, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock118 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, -1, -1, 2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints118 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables118 q).1 (blockVariables118 q).2
  have hx : blockA118.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA118 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA118, blockConstraints118, DerivationConstraint.evaluate, x,
        blockVariables118, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA118 blockB118
    blockLeftInverse118 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![1, -1, -1, 2]
  · obtain ⟨q, hq'⟩ := (blockSupport118 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables119 : Fin 2 → Fin 26 × Fin 26 :=
  ![(10, 9), (16, 15)]
private def blockConstraints119 : Fin 2 → DerivationConstraint :=
  ![.entry 1 0 9, .entry 1 3 15]
private def blockA119 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 0], ![0, 1]]
private def blockB119 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 0], ![0, 1]]

private theorem blockLeftInverse119 : blockB119 * blockA119 = 1 := by
  decide +kernel

private theorem blockSupport119 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![1, -1, -1, 3] k) ↔ ∃ q, blockVariables119 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 119, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock119 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, -1, -1, 3] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints119 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables119 q).1 (blockVariables119 q).2
  have hx : blockA119.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA119 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA119, blockConstraints119, DerivationConstraint.evaluate, x,
        blockVariables119, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA119 blockB119
    blockLeftInverse119 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![1, -1, -1, 3]
  · obtain ⟨q, hq'⟩ := (blockSupport119 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables120 : Fin 6 → Fin 26 × Fin 26 :=
  ![(16, 0), (19, 1), (21, 2), (23, 4), (24, 6), (25, 9)]
private def blockConstraints120 : Fin 6 → DerivationConstraint :=
  ![.entry 0 3 1, .entry 0 5 2, .entry 0 8 4, .entry 0 10 6, .entry 0 12 9, .quotient 24]
private def blockA120 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ![![1, 1, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0],
      ![1, 0, 0, 0, 0, 1], ![1, 0, 0, 0, 0, 0]]
private def blockB120 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 1], ![1, 0, 0, 0, 0, 1], ![0, 1, 0, 0, 0, 1], ![0, 0, 1, 0, 0, 1],
      ![0, 0, 0, 1, 0, 1], ![0, 0, 0, 0, 1, 1]]

private theorem blockLeftInverse120 : blockB120 * blockA120 = 1 := by
  decide +kernel

private theorem blockSupport120 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![1, -1, 0, 0] k) ↔ ∃ q, blockVariables120 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 120, a root degree with 6 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock120 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, -1, 0, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 6) : (blockConstraints120 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 6 → R := fun q => X (blockVariables120 q).1 (blockVariables120 q).2
  have hx : blockA120.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA120 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA120, blockConstraints120, DerivationConstraint.evaluate, x,
        blockVariables120, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA120 blockB120
    blockLeftInverse120 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![1, -1, 0, 0]
  · obtain ⟨q, hq'⟩ := (blockSupport120 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables121 : Fin 12 → Fin 26 × Fin 26 :=
  ![(3, 1), (5, 2), (8, 4), (10, 6), (12, 9), (13, 9), (16, 12), (16, 13), (19, 15), (21, 17),
      (23, 20), (24, 22)]
private def blockConstraints121 : Fin 12 → DerivationConstraint :=
  ![.entry 0 0 9, .entry 0 3 15, .entry 0 5 17, .entry 0 8 20, .entry 0 10 22, .entry 0 16 25,
      .entry 1 0 6, .entry 1 1 9, .entry 1 3 13, .entry 1 5 14, .entry 1 8 18, .ideal 16]
private def blockA121 : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
      ![0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0],
      ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
      ![1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0],
      ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
private def blockB121 : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1],
      ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1],
      ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1],
      ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1], ![0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1]]

private theorem blockLeftInverse121 : blockB121 * blockA121 = 1 := by
  decide +kernel

private theorem blockSupport121 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![1, -1, 0, 1] k) ↔ ∃ q, blockVariables121 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 121, a root degree with 12 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock121 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, -1, 0, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 12) : (blockConstraints121 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 12 → R := fun q => X (blockVariables121 q).1 (blockVariables121 q).2
  have hx : blockA121.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA121 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA121, blockConstraints121, DerivationConstraint.evaluate, x,
        blockVariables121, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA121 blockB121
    blockLeftInverse121 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![1, -1, 0, 1]
  · obtain ⟨q, hq'⟩ := (blockSupport121 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables122 : Fin 6 → Fin 26 × Fin 26 :=
  ![(0, 9), (3, 15), (5, 17), (8, 20), (10, 22), (16, 25)]
private def blockConstraints122 : Fin 6 → DerivationConstraint :=
  ![.entry 1 0 22, .entry 1 3 25, .entry 2 0 20, .entry 2 5 25, .entry 4 0 17, .quotient 5]
private def blockA122 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ![![1, 0, 0, 0, 1, 0], ![0, 1, 0, 0, 0, 1], ![1, 0, 0, 1, 0, 0], ![0, 0, 1, 0, 0, 1],
      ![1, 0, 1, 0, 0, 0], ![1, 0, 0, 0, 0, 0]]
private def blockB122 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 1], ![0, 1, 0, 1, 1, 1], ![0, 0, 0, 0, 1, 1], ![0, 0, 1, 0, 0, 1],
      ![1, 0, 0, 0, 0, 1], ![0, 0, 0, 1, 1, 1]]

private theorem blockLeftInverse122 : blockB122 * blockA122 = 1 := by
  decide +kernel

private theorem blockSupport122 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![1, -1, 0, 2] k) ↔ ∃ q, blockVariables122 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 122, a root degree with 6 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock122 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, -1, 0, 2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 6) : (blockConstraints122 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 6 → R := fun q => X (blockVariables122 q).1 (blockVariables122 q).2
  have hx : blockA122.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA122 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA122, blockConstraints122, DerivationConstraint.evaluate, x,
        blockVariables122, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA122 blockB122
    blockLeftInverse122 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![1, -1, 0, 2]
  · obtain ⟨q, hq'⟩ := (blockSupport122 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables123 : Fin 2 → Fin 26 × Fin 26 :=
  ![(19, 0), (25, 6)]
private def blockConstraints123 : Fin 2 → DerivationConstraint :=
  ![.entry 0 7 2, .entry 0 12 6]
private def blockA123 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 0], ![1, 1]]
private def blockB123 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 0], ![1, 1]]

private theorem blockLeftInverse123 : blockB123 * blockA123 = 1 := by
  decide +kernel

private theorem blockSupport123 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![1, -1, 1, -2] k) ↔ ∃ q, blockVariables123 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 123, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock123 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, -1, 1, -2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints123 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables123 q).1 (blockVariables123 q).2
  have hx : blockA123.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA123 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA123, blockConstraints123, DerivationConstraint.evaluate, x,
        blockVariables123, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA123 blockB123
    blockLeftInverse123 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![1, -1, 1, -2]
  · obtain ⟨q, hq'⟩ := (blockSupport123 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables124 : Fin 12 → Fin 26 × Fin 26 :=
  ![(3, 0), (7, 2), (11, 4), (12, 6), (13, 6), (15, 9), (16, 10), (19, 12), (19, 13), (21, 14),
      (23, 18), (25, 22)]
private def blockConstraints124 : Fin 12 → DerivationConstraint :=
  ![.entry 0 0 6, .entry 0 1 9, .entry 0 3 12, .entry 0 3 13, .entry 0 5 14, .entry 0 7 17,
      .entry 0 8 18, .entry 0 11 20, .entry 0 12 22, .entry 0 16 24, .entry 1 1 6, .ideal 19]
private def blockA124 : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ![![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
      ![1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
      ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
private def blockB124 : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1],
      ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
      ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1],
      ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1], ![1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1]]

private theorem blockLeftInverse124 : blockB124 * blockA124 = 1 := by
  decide +kernel

private theorem blockSupport124 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![1, -1, 1, -1] k) ↔ ∃ q, blockVariables124 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 124, a root degree with 12 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock124 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, -1, 1, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 12) : (blockConstraints124 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 12 → R := fun q => X (blockVariables124 q).1 (blockVariables124 q).2
  have hx : blockA124.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA124 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA124, blockConstraints124, DerivationConstraint.evaluate, x,
        blockVariables124, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA124 blockB124
    blockLeftInverse124 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![1, -1, 1, -1]
  · obtain ⟨q, hq'⟩ := (blockSupport124 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables125 : Fin 12 → Fin 26 × Fin 26 :=
  ![(0, 6), (1, 9), (3, 12), (3, 13), (5, 14), (7, 17), (8, 18), (11, 20), (12, 22), (13, 22),
      (16, 24), (19, 25)]
private def blockConstraints125 : Fin 12 → DerivationConstraint :=
  ![.entry 0 0 22, .entry 0 3 25, .entry 1 1 22, .entry 1 3 24, .entry 2 0 18, .entry 2 1 20,
      .entry 2 2 22, .entry 2 3 23, .entry 2 5 24, .entry 2 7 25, .entry 4 0 14, .ideal 3]
private def blockA125 : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      ![0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0], ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0],
      ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1],
      ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
private def blockB125 : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1],
      ![0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 1], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1], ![0, 1, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1],
      ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1], ![1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1],
      ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1], ![0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 1, 1]]

private theorem blockLeftInverse125 : blockB125 * blockA125 = 1 := by
  decide +kernel

private theorem blockSupport125 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![1, -1, 1, 0] k) ↔ ∃ q, blockVariables125 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 125, a root degree with 12 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock125 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, -1, 1, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 12) : (blockConstraints125 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 12 → R := fun q => X (blockVariables125 q).1 (blockVariables125 q).2
  have hx : blockA125.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA125 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA125, blockConstraints125, DerivationConstraint.evaluate, x,
        blockVariables125, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA125 blockB125
    blockLeftInverse125 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![1, -1, 1, 0]
  · obtain ⟨q, hq'⟩ := (blockSupport125 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd


end TauCeti.F4ShortRoot
