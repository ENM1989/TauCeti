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

private def blockVariables154 : Fin 1 → Fin 26 × Fin 26 :=
  ![(3, 22)]
private def blockConstraints154 : Fin 1 → DerivationConstraint :=
  ![.entry 6 0 22]
private def blockA154 : Matrix (Fin 1) (Fin 1) (ZMod 2) :=
  ![![1]]
private def blockB154 : Matrix (Fin 1) (Fin 1) (ZMod 2) :=
  ![![1]]

private theorem blockLeftInverse154 : blockB154 * blockA154 = 1 := by
  decide +kernel

private theorem blockSupport154 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![2, -2, 2, 0] k) ↔ ∃ q, blockVariables154 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 154, a nonroot degree with 1 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock154 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![2, -2, 2, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 1) : (blockConstraints154 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 1 → R := fun q => X (blockVariables154 q).1 (blockVariables154 q).2
  have hx : blockA154.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA154 r i) * x i = 0
    have h := hc r
    fin_cases r; simp [blockA154, blockConstraints154, DerivationConstraint.evaluate, x,
        blockVariables154, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA154 blockB154
    blockLeftInverse154 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![2, -2, 2, 0]
  · obtain ⟨q, hq'⟩ := (blockSupport154 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables155 : Fin 2 → Fin 26 × Fin 26 :=
  ![(16, 4), (21, 9)]
private def blockConstraints155 : Fin 2 → DerivationConstraint :=
  ![.entry 0 5 9, .entry 0 16 20]
private def blockA155 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]
private def blockB155 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]

private theorem blockLeftInverse155 : blockB155 * blockA155 = 1 := by
  decide +kernel

private theorem blockSupport155 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![2, -1, -1, 1] k) ↔ ∃ q, blockVariables155 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 155, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock155 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![2, -1, -1, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints155 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables155 q).1 (blockVariables155 q).2
  have hx : blockA155.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA155 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA155, blockConstraints155, DerivationConstraint.evaluate, x,
        blockVariables155, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA155 blockB155
    blockLeftInverse155 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![2, -1, -1, 1]
  · obtain ⟨q, hq'⟩ := (blockSupport155 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables156 : Fin 2 → Fin 26 × Fin 26 :=
  ![(5, 9), (16, 20)]
private def blockConstraints156 : Fin 2 → DerivationConstraint :=
  ![.entry 1 3 20, .entry 1 5 22]
private def blockA156 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]
private def blockB156 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]

private theorem blockLeftInverse156 : blockB156 * blockA156 = 1 := by
  decide +kernel

private theorem blockSupport156 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![2, -1, -1, 2] k) ↔ ∃ q, blockVariables156 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 156, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock156 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![2, -1, -1, 2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints156 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables156 q).1 (blockVariables156 q).2
  have hx : blockA156.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA156 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA156, blockConstraints156, DerivationConstraint.evaluate, x,
        blockVariables156, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA156 blockB156
    blockLeftInverse156 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![2, -1, -1, 2]
  · obtain ⟨q, hq'⟩ := (blockSupport156 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables157 : Fin 2 → Fin 26 × Fin 26 :=
  ![(19, 4), (21, 6)]
private def blockConstraints157 : Fin 2 → DerivationConstraint :=
  ![.entry 0 3 4, .entry 0 5 6]
private def blockA157 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 0], ![0, 1]]
private def blockB157 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 0], ![0, 1]]

private theorem blockLeftInverse157 : blockB157 * blockA157 = 1 := by
  decide +kernel

private theorem blockSupport157 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![2, -1, 0, -1] k) ↔ ∃ q, blockVariables157 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 157, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock157 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![2, -1, 0, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints157 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables157 q).1 (blockVariables157 q).2
  have hx : blockA157.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA157 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA157, blockConstraints157, DerivationConstraint.evaluate, x,
        blockVariables157, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA157 blockB157
    blockLeftInverse157 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![2, -1, 0, -1]
  · obtain ⟨q, hq'⟩ := (blockSupport157 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables158 : Fin 6 → Fin 26 × Fin 26 :=
  ![(3, 4), (5, 6), (7, 9), (16, 18), (19, 20), (21, 22)]
private def blockConstraints158 : Fin 6 → DerivationConstraint :=
  ![.entry 0 3 20, .entry 0 5 22, .entry 1 3 18, .entry 1 7 22, .entry 2 5 18, .quotient 10]
private def blockA158 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ![![1, 0, 0, 0, 1, 0], ![0, 1, 0, 0, 0, 1], ![1, 0, 0, 1, 0, 0], ![0, 0, 1, 0, 0, 1],
      ![0, 1, 0, 1, 0, 0], ![1, 0, 0, 0, 0, 0]]
private def blockB158 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 1], ![0, 0, 1, 0, 1, 1], ![0, 1, 1, 1, 1, 1], ![0, 0, 1, 0, 0, 1],
      ![1, 0, 0, 0, 0, 1], ![0, 1, 1, 0, 1, 1]]

private theorem blockLeftInverse158 : blockB158 * blockA158 = 1 := by
  decide +kernel

private theorem blockSupport158 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![2, -1, 0, 0] k) ↔ ∃ q, blockVariables158 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 158, a root degree with 6 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock158 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![2, -1, 0, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 6) : (blockConstraints158 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 6 → R := fun q => X (blockVariables158 q).1 (blockVariables158 q).2
  have hx : blockA158.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA158 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA158, blockConstraints158, DerivationConstraint.evaluate, x,
        blockVariables158, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA158 blockB158
    blockLeftInverse158 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![2, -1, 0, 0]
  · obtain ⟨q, hq'⟩ := (blockSupport158 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables159 : Fin 2 → Fin 26 × Fin 26 :=
  ![(3, 20), (5, 22)]
private def blockConstraints159 : Fin 2 → DerivationConstraint :=
  ![.entry 4 0 22, .entry 4 3 25]
private def blockA159 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]
private def blockB159 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]

private theorem blockLeftInverse159 : blockB159 * blockA159 = 1 := by
  decide +kernel

private theorem blockSupport159 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![2, -1, 0, 1] k) ↔ ∃ q, blockVariables159 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 159, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock159 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![2, -1, 0, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints159 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables159 q).1 (blockVariables159 q).2
  have hx : blockA159.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA159 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA159, blockConstraints159, DerivationConstraint.evaluate, x,
        blockVariables159, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA159 blockB159
    blockLeftInverse159 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![2, -1, 0, 1]
  · obtain ⟨q, hq'⟩ := (blockSupport159 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables160 : Fin 2 → Fin 26 × Fin 26 :=
  ![(7, 6), (19, 18)]
private def blockConstraints160 : Fin 2 → DerivationConstraint :=
  ![.entry 0 3 18, .entry 0 7 22]
private def blockA160 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]
private def blockB160 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]

private theorem blockLeftInverse160 : blockB160 * blockA160 = 1 := by
  decide +kernel

private theorem blockSupport160 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![2, -1, 1, -2] k) ↔ ∃ q, blockVariables160 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 160, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock160 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![2, -1, 1, -2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints160 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables160 q).1 (blockVariables160 q).2
  have hx : blockA160.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA160 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA160, blockConstraints160, DerivationConstraint.evaluate, x,
        blockVariables160, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA160 blockB160
    blockLeftInverse160 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![2, -1, 1, -2]
  · obtain ⟨q, hq'⟩ := (blockSupport160 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables161 : Fin 2 → Fin 26 × Fin 26 :=
  ![(3, 18), (7, 22)]
private def blockConstraints161 : Fin 2 → DerivationConstraint :=
  ![.entry 4 1 22, .entry 4 3 24]
private def blockA161 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]
private def blockB161 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]

private theorem blockLeftInverse161 : blockB161 * blockA161 = 1 := by
  decide +kernel

private theorem blockSupport161 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![2, -1, 1, -1] k) ↔ ∃ q, blockVariables161 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 161, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock161 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![2, -1, 1, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints161 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables161 q).1 (blockVariables161 q).2
  have hx : blockA161.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA161 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA161, blockConstraints161, DerivationConstraint.evaluate, x,
        blockVariables161, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA161 blockB161
    blockLeftInverse161 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![2, -1, 1, -1]
  · obtain ⟨q, hq'⟩ := (blockSupport161 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables162 : Fin 1 → Fin 26 × Fin 26 :=
  ![(21, 4)]
private def blockConstraints162 : Fin 1 → DerivationConstraint :=
  ![.entry 0 5 4]
private def blockA162 : Matrix (Fin 1) (Fin 1) (ZMod 2) :=
  ![![1]]
private def blockB162 : Matrix (Fin 1) (Fin 1) (ZMod 2) :=
  ![![1]]

private theorem blockLeftInverse162 : blockB162 * blockA162 = 1 := by
  decide +kernel

private theorem blockSupport162 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![2, 0, -2, 0] k) ↔ ∃ q, blockVariables162 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 162, a nonroot degree with 1 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock162 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![2, 0, -2, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 1) : (blockConstraints162 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 1 → R := fun q => X (blockVariables162 q).1 (blockVariables162 q).2
  have hx : blockA162.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA162 r i) * x i = 0
    have h := hc r
    fin_cases r; simp [blockA162, blockConstraints162, DerivationConstraint.evaluate, x,
        blockVariables162, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA162 blockB162
    blockLeftInverse162 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![2, 0, -2, 0]
  · obtain ⟨q, hq'⟩ := (blockSupport162 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables163 : Fin 2 → Fin 26 × Fin 26 :=
  ![(5, 4), (21, 20)]
private def blockConstraints163 : Fin 2 → DerivationConstraint :=
  ![.entry 0 5 20, .entry 1 5 18]
private def blockA163 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 1], ![1, 0]]
private def blockB163 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 1]]

private theorem blockLeftInverse163 : blockB163 * blockA163 = 1 := by
  decide +kernel

private theorem blockSupport163 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![2, 0, -2, 1] k) ↔ ∃ q, blockVariables163 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 163, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock163 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![2, 0, -2, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints163 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables163 q).1 (blockVariables163 q).2
  have hx : blockA163.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA163 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA163, blockConstraints163, DerivationConstraint.evaluate, x,
        blockVariables163, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA163 blockB163
    blockLeftInverse163 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![2, 0, -2, 1]
  · obtain ⟨q, hq'⟩ := (blockSupport163 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables164 : Fin 1 → Fin 26 × Fin 26 :=
  ![(5, 20)]
private def blockConstraints164 : Fin 1 → DerivationConstraint :=
  ![.entry 4 0 20]
private def blockA164 : Matrix (Fin 1) (Fin 1) (ZMod 2) :=
  ![![1]]
private def blockB164 : Matrix (Fin 1) (Fin 1) (ZMod 2) :=
  ![![1]]

private theorem blockLeftInverse164 : blockB164 * blockA164 = 1 := by
  decide +kernel

private theorem blockSupport164 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![2, 0, -2, 2] k) ↔ ∃ q, blockVariables164 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 164, a nonroot degree with 1 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock164 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![2, 0, -2, 2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 1) : (blockConstraints164 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 1 → R := fun q => X (blockVariables164 q).1 (blockVariables164 q).2
  have hx : blockA164.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA164 r i) * x i = 0
    have h := hc r
    fin_cases r; simp [blockA164, blockConstraints164, DerivationConstraint.evaluate, x,
        blockVariables164, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA164 blockB164
    blockLeftInverse164 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![2, 0, -2, 2]
  · obtain ⟨q, hq'⟩ := (blockSupport164 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables165 : Fin 2 → Fin 26 × Fin 26 :=
  ![(7, 4), (21, 18)]
private def blockConstraints165 : Fin 2 → DerivationConstraint :=
  ![.entry 0 5 18, .entry 0 7 20]
private def blockA165 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]
private def blockB165 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]

private theorem blockLeftInverse165 : blockB165 * blockA165 = 1 := by
  decide +kernel

private theorem blockSupport165 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![2, 0, -1, -1] k) ↔ ∃ q, blockVariables165 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 165, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock165 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![2, 0, -1, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints165 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables165 q).1 (blockVariables165 q).2
  have hx : blockA165.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA165 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA165, blockConstraints165, DerivationConstraint.evaluate, x,
        blockVariables165, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA165 blockB165
    blockLeftInverse165 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![2, 0, -1, -1]
  · obtain ⟨q, hq'⟩ := (blockSupport165 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables166 : Fin 2 → Fin 26 × Fin 26 :=
  ![(5, 18), (7, 20)]
private def blockConstraints166 : Fin 2 → DerivationConstraint :=
  ![.entry 4 0 18, .entry 4 1 20]
private def blockA166 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 0], ![0, 1]]
private def blockB166 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 0], ![0, 1]]

private theorem blockLeftInverse166 : blockB166 * blockA166 = 1 := by
  decide +kernel

private theorem blockSupport166 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![2, 0, -1, 0] k) ↔ ∃ q, blockVariables166 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 166, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock166 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![2, 0, -1, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints166 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables166 q).1 (blockVariables166 q).2
  have hx : blockA166.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA166 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA166, blockConstraints166, DerivationConstraint.evaluate, x,
        blockVariables166, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA166 blockB166
    blockLeftInverse166 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![2, 0, -1, 0]
  · obtain ⟨q, hq'⟩ := (blockSupport166 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables167 : Fin 1 → Fin 26 × Fin 26 :=
  ![(7, 18)]
private def blockConstraints167 : Fin 1 → DerivationConstraint :=
  ![.entry 4 1 18]
private def blockA167 : Matrix (Fin 1) (Fin 1) (ZMod 2) :=
  ![![1]]
private def blockB167 : Matrix (Fin 1) (Fin 1) (ZMod 2) :=
  ![![1]]

private theorem blockLeftInverse167 : blockB167 * blockA167 = 1 := by
  decide +kernel

private theorem blockSupport167 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![2, 0, 0, -2] k) ↔ ∃ q, blockVariables167 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 167, a nonroot degree with 1 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock167 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![2, 0, 0, -2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 1) : (blockConstraints167 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 1 → R := fun q => X (blockVariables167 q).1 (blockVariables167 q).2
  have hx : blockA167.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA167 r i) * x i = 0
    have h := hc r
    fin_cases r; simp [blockA167, blockConstraints167, DerivationConstraint.evaluate, x,
        blockVariables167, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA167 blockB167
    blockLeftInverse167 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![2, 0, 0, -2]
  · obtain ⟨q, hq'⟩ := (blockSupport167 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd


end TauCeti.F4ShortRoot
