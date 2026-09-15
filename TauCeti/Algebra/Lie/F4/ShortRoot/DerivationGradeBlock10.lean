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

private def blockVariables140 : Fin 2 → Fin 26 × Fin 26 :=
  ![(7, 10), (15, 18)]
private def blockConstraints140 : Fin 2 → DerivationConstraint :=
  ![.entry 0 1 18, .entry 0 7 24]
private def blockA140 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]
private def blockB140 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]

private theorem blockLeftInverse140 : blockB140 * blockA140 = 1 := by
  decide +kernel

private theorem blockSupport140 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![1, 0, 1, -3] k) ↔ ∃ q, blockVariables140 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 140, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock140 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, 0, 1, -3] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints140 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables140 q).1 (blockVariables140 q).2
  have hx : blockA140.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA140 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA140, blockConstraints140, DerivationConstraint.evaluate, x,
        blockVariables140, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA140 blockB140
    blockLeftInverse140 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![1, 0, 1, -3]
  · obtain ⟨q, hq'⟩ := (blockSupport140 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables141 : Fin 2 → Fin 26 × Fin 26 :=
  ![(1, 18), (7, 24)]
private def blockConstraints141 : Fin 2 → DerivationConstraint :=
  ![.entry 4 1 24, .entry 6 1 23]
private def blockA141 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 1], ![1, 0]]
private def blockB141 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 1]]

private theorem blockLeftInverse141 : blockB141 * blockA141 = 1 := by
  decide +kernel

private theorem blockSupport141 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![1, 0, 1, -2] k) ↔ ∃ q, blockVariables141 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 141, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock141 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, 0, 1, -2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints141 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables141 q).1 (blockVariables141 q).2
  have hx : blockA141.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA141 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA141, blockConstraints141, DerivationConstraint.evaluate, x,
        blockVariables141, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA141 blockB141
    blockLeftInverse141 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![1, 0, 1, -2]
  · obtain ⟨q, hq'⟩ := (blockSupport141 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables142 : Fin 2 → Fin 26 × Fin 26 :=
  ![(14, 4), (21, 11)]
private def blockConstraints142 : Fin 2 → DerivationConstraint :=
  ![.entry 0 5 11, .entry 0 14 20]
private def blockA142 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]
private def blockB142 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]

private theorem blockLeftInverse142 : blockB142 * blockA142 = 1 := by
  decide +kernel

private theorem blockSupport142 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![1, 1, -3, 1] k) ↔ ∃ q, blockVariables142 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 142, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock142 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, 1, -3, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints142 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables142 q).1 (blockVariables142 q).2
  have hx : blockA142.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA142 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA142, blockConstraints142, DerivationConstraint.evaluate, x,
        blockVariables142, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA142 blockB142
    blockLeftInverse142 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![1, 1, -3, 1]
  · obtain ⟨q, hq'⟩ := (blockSupport142 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables143 : Fin 2 → Fin 26 × Fin 26 :=
  ![(5, 11), (14, 20)]
private def blockConstraints143 : Fin 2 → DerivationConstraint :=
  ![.entry 1 2 20, .entry 1 5 23]
private def blockA143 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]
private def blockB143 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]

private theorem blockLeftInverse143 : blockB143 * blockA143 = 1 := by
  decide +kernel

private theorem blockSupport143 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![1, 1, -3, 2] k) ↔ ∃ q, blockVariables143 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 143, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock143 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, 1, -3, 2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints143 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables143 q).1 (blockVariables143 q).2
  have hx : blockA143.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA143 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA143, blockConstraints143, DerivationConstraint.evaluate, x,
        blockVariables143, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA143 blockB143
    blockLeftInverse143 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![1, 1, -3, 2]
  · obtain ⟨q, hq'⟩ := (blockSupport143 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables144 : Fin 2 → Fin 26 × Fin 26 :=
  ![(17, 4), (21, 8)]
private def blockConstraints144 : Fin 2 → DerivationConstraint :=
  ![.entry 0 2 4, .entry 0 5 8]
private def blockA144 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 0], ![0, 1]]
private def blockB144 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 0], ![0, 1]]

private theorem blockLeftInverse144 : blockB144 * blockA144 = 1 := by
  decide +kernel

private theorem blockSupport144 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![1, 1, -2, -1] k) ↔ ∃ q, blockVariables144 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 144, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock144 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, 1, -2, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints144 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables144 q).1 (blockVariables144 q).2
  have hx : blockA144.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA144 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA144, blockConstraints144, DerivationConstraint.evaluate, x,
        blockVariables144, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA144 blockB144
    blockLeftInverse144 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![1, 1, -2, -1]
  · obtain ⟨q, hq'⟩ := (blockSupport144 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables145 : Fin 6 → Fin 26 × Fin 26 :=
  ![(2, 4), (5, 8), (7, 11), (14, 18), (17, 20), (21, 23)]
private def blockConstraints145 : Fin 6 → DerivationConstraint :=
  ![.entry 0 2 20, .entry 0 5 23, .entry 1 2 18, .entry 1 7 23, .entry 3 5 18, .quotient 8]
private def blockA145 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ![![1, 0, 0, 0, 1, 0], ![0, 1, 0, 0, 0, 1], ![1, 0, 0, 1, 0, 0], ![0, 0, 1, 0, 0, 1],
      ![0, 1, 0, 1, 0, 0], ![1, 0, 0, 0, 0, 0]]
private def blockB145 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 1], ![0, 0, 1, 0, 1, 1], ![0, 1, 1, 1, 1, 1], ![0, 0, 1, 0, 0, 1],
      ![1, 0, 0, 0, 0, 1], ![0, 1, 1, 0, 1, 1]]

private theorem blockLeftInverse145 : blockB145 * blockA145 = 1 := by
  decide +kernel

private theorem blockSupport145 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![1, 1, -2, 0] k) ↔ ∃ q, blockVariables145 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 145, a root degree with 6 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock145 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, 1, -2, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 6) : (blockConstraints145 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 6 → R := fun q => X (blockVariables145 q).1 (blockVariables145 q).2
  have hx : blockA145.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA145 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA145, blockConstraints145, DerivationConstraint.evaluate, x,
        blockVariables145, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA145 blockB145
    blockLeftInverse145 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![1, 1, -2, 0]
  · obtain ⟨q, hq'⟩ := (blockSupport145 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables146 : Fin 2 → Fin 26 × Fin 26 :=
  ![(2, 20), (5, 23)]
private def blockConstraints146 : Fin 2 → DerivationConstraint :=
  ![.entry 4 0 23, .entry 4 2 25]
private def blockA146 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]
private def blockB146 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]

private theorem blockLeftInverse146 : blockB146 * blockA146 = 1 := by
  decide +kernel

private theorem blockSupport146 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![1, 1, -2, 1] k) ↔ ∃ q, blockVariables146 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 146, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock146 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, 1, -2, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints146 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables146 q).1 (blockVariables146 q).2
  have hx : blockA146.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA146 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA146, blockConstraints146, DerivationConstraint.evaluate, x,
        blockVariables146, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA146 blockB146
    blockLeftInverse146 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![1, 1, -2, 1]
  · obtain ⟨q, hq'⟩ := (blockSupport146 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables147 : Fin 2 → Fin 26 × Fin 26 :=
  ![(7, 8), (17, 18)]
private def blockConstraints147 : Fin 2 → DerivationConstraint :=
  ![.entry 0 2 18, .entry 0 7 23]
private def blockA147 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]
private def blockB147 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]

private theorem blockLeftInverse147 : blockB147 * blockA147 = 1 := by
  decide +kernel

private theorem blockSupport147 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![1, 1, -1, -2] k) ↔ ∃ q, blockVariables147 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 147, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock147 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, 1, -1, -2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints147 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables147 q).1 (blockVariables147 q).2
  have hx : blockA147.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA147 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA147, blockConstraints147, DerivationConstraint.evaluate, x,
        blockVariables147, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA147 blockB147
    blockLeftInverse147 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![1, 1, -1, -2]
  · obtain ⟨q, hq'⟩ := (blockSupport147 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables148 : Fin 2 → Fin 26 × Fin 26 :=
  ![(2, 18), (7, 23)]
private def blockConstraints148 : Fin 2 → DerivationConstraint :=
  ![.entry 4 1 23, .entry 4 2 24]
private def blockA148 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]
private def blockB148 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]

private theorem blockLeftInverse148 : blockB148 * blockA148 = 1 := by
  decide +kernel

private theorem blockSupport148 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![1, 1, -1, -1] k) ↔ ∃ q, blockVariables148 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 148, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock148 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, 1, -1, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints148 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables148 q).1 (blockVariables148 q).2
  have hx : blockA148.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA148 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA148, blockConstraints148, DerivationConstraint.evaluate, x,
        blockVariables148, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA148 blockB148
    blockLeftInverse148 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![1, 1, -1, -1]
  · obtain ⟨q, hq'⟩ := (blockSupport148 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables149 : Fin 1 → Fin 26 × Fin 26 :=
  ![(16, 9)]
private def blockConstraints149 : Fin 1 → DerivationConstraint :=
  ![.entry 1 3 9]
private def blockA149 : Matrix (Fin 1) (Fin 1) (ZMod 2) :=
  ![![1]]
private def blockB149 : Matrix (Fin 1) (Fin 1) (ZMod 2) :=
  ![![1]]

private theorem blockLeftInverse149 : blockB149 * blockA149 = 1 := by
  decide +kernel

private theorem blockSupport149 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![2, -2, 0, 2] k) ↔ ∃ q, blockVariables149 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 149, a nonroot degree with 1 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock149 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![2, -2, 0, 2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 1) : (blockConstraints149 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 1 → R := fun q => X (blockVariables149 q).1 (blockVariables149 q).2
  have hx : blockA149.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA149 r i) * x i = 0
    have h := hc r
    fin_cases r; simp [blockA149, blockConstraints149, DerivationConstraint.evaluate, x,
        blockVariables149, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA149 blockB149
    blockLeftInverse149 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![2, -2, 0, 2]
  · obtain ⟨q, hq'⟩ := (blockSupport149 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables150 : Fin 2 → Fin 26 × Fin 26 :=
  ![(16, 6), (19, 9)]
private def blockConstraints150 : Fin 2 → DerivationConstraint :=
  ![.entry 0 3 9, .entry 0 16 22]
private def blockA150 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]
private def blockB150 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]

private theorem blockLeftInverse150 : blockB150 * blockA150 = 1 := by
  decide +kernel

private theorem blockSupport150 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![2, -2, 1, 0] k) ↔ ∃ q, blockVariables150 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 150, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock150 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![2, -2, 1, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints150 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables150 q).1 (blockVariables150 q).2
  have hx : blockA150.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA150 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA150, blockConstraints150, DerivationConstraint.evaluate, x,
        blockVariables150, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA150 blockB150
    blockLeftInverse150 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![2, -2, 1, 0]
  · obtain ⟨q, hq'⟩ := (blockSupport150 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables151 : Fin 2 → Fin 26 × Fin 26 :=
  ![(3, 9), (16, 22)]
private def blockConstraints151 : Fin 2 → DerivationConstraint :=
  ![.entry 1 3 22, .entry 2 3 20]
private def blockA151 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 1], ![1, 0]]
private def blockB151 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 1]]

private theorem blockLeftInverse151 : blockB151 * blockA151 = 1 := by
  decide +kernel

private theorem blockSupport151 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![2, -2, 1, 1] k) ↔ ∃ q, blockVariables151 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 151, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock151 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![2, -2, 1, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints151 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables151 q).1 (blockVariables151 q).2
  have hx : blockA151.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA151 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA151, blockConstraints151, DerivationConstraint.evaluate, x,
        blockVariables151, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA151 blockB151
    blockLeftInverse151 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![2, -2, 1, 1]
  · obtain ⟨q, hq'⟩ := (blockSupport151 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables152 : Fin 1 → Fin 26 × Fin 26 :=
  ![(19, 6)]
private def blockConstraints152 : Fin 1 → DerivationConstraint :=
  ![.entry 0 3 6]
private def blockA152 : Matrix (Fin 1) (Fin 1) (ZMod 2) :=
  ![![1]]
private def blockB152 : Matrix (Fin 1) (Fin 1) (ZMod 2) :=
  ![![1]]

private theorem blockLeftInverse152 : blockB152 * blockA152 = 1 := by
  decide +kernel

private theorem blockSupport152 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![2, -2, 2, -2] k) ↔ ∃ q, blockVariables152 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 152, a nonroot degree with 1 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock152 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![2, -2, 2, -2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 1) : (blockConstraints152 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 1 → R := fun q => X (blockVariables152 q).1 (blockVariables152 q).2
  have hx : blockA152.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA152 r i) * x i = 0
    have h := hc r
    fin_cases r; simp [blockA152, blockConstraints152, DerivationConstraint.evaluate, x,
        blockVariables152, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA152 blockB152
    blockLeftInverse152 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![2, -2, 2, -2]
  · obtain ⟨q, hq'⟩ := (blockSupport152 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables153 : Fin 2 → Fin 26 × Fin 26 :=
  ![(3, 6), (19, 22)]
private def blockConstraints153 : Fin 2 → DerivationConstraint :=
  ![.entry 0 3 22, .entry 2 3 18]
private def blockA153 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 1], ![1, 0]]
private def blockB153 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 1]]

private theorem blockLeftInverse153 : blockB153 * blockA153 = 1 := by
  decide +kernel

private theorem blockSupport153 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![2, -2, 2, -1] k) ↔ ∃ q, blockVariables153 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 153, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock153 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![2, -2, 2, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints153 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables153 q).1 (blockVariables153 q).2
  have hx : blockA153.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA153 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA153, blockConstraints153, DerivationConstraint.evaluate, x,
        blockVariables153, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA153 blockB153
    blockLeftInverse153 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![2, -2, 2, -1]
  · obtain ⟨q, hq'⟩ := (blockSupport153 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd


end TauCeti.F4ShortRoot
