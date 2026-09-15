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

private def blockVariables056 : Fin 2 → Fin 26 × Fin 26 :=
  ![(2, 16), (9, 23)]
private def blockConstraints056 : Fin 2 → DerivationConstraint :=
  ![.entry 3 1 23, .entry 3 2 24]
private def blockA056 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]
private def blockB056 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]

private theorem blockLeftInverse056 : blockB056 * blockA056 = 1 := by
  decide +kernel

private theorem blockSupport056 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![-1, 2, -1, -1] k) ↔ ∃ q, blockVariables056 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 56, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock056 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 2, -1, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints056 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables056 q).1 (blockVariables056 q).2
  have hx : blockA056.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA056 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA056, blockConstraints056, DerivationConstraint.evaluate, x,
        blockVariables056, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA056 blockB056
    blockLeftInverse056 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![-1, 2, -1, -1]
  · obtain ⟨q, hq'⟩ := (blockSupport056 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables057 : Fin 1 → Fin 26 × Fin 26 :=
  ![(23, 2)]
private def blockConstraints057 : Fin 1 → DerivationConstraint :=
  ![.entry 0 8 2]
private def blockA057 : Matrix (Fin 1) (Fin 1) (ZMod 2) :=
  ![![1]]
private def blockB057 : Matrix (Fin 1) (Fin 1) (ZMod 2) :=
  ![![1]]

private theorem blockLeftInverse057 : blockB057 * blockA057 = 1 := by
  decide +kernel

private theorem blockSupport057 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![0, -2, 2, 0] k) ↔ ∃ q, blockVariables057 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 57, a nonroot degree with 1 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock057 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, -2, 2, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 1) : (blockConstraints057 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 1 → R := fun q => X (blockVariables057 q).1 (blockVariables057 q).2
  have hx : blockA057.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA057 r i) * x i = 0
    have h := hc r
    fin_cases r; simp [blockA057, blockConstraints057, DerivationConstraint.evaluate, x,
        blockVariables057, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA057 blockB057
    blockLeftInverse057 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![0, -2, 2, 0]
  · obtain ⟨q, hq'⟩ := (blockSupport057 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables058 : Fin 2 → Fin 26 × Fin 26 :=
  ![(8, 2), (23, 17)]
private def blockConstraints058 : Fin 2 → DerivationConstraint :=
  ![.entry 0 8 17, .entry 1 8 14]
private def blockA058 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 1], ![1, 0]]
private def blockB058 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 1]]

private theorem blockLeftInverse058 : blockB058 * blockA058 = 1 := by
  decide +kernel

private theorem blockSupport058 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![0, -2, 2, 1] k) ↔ ∃ q, blockVariables058 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 58, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock058 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, -2, 2, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints058 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables058 q).1 (blockVariables058 q).2
  have hx : blockA058.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA058 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA058, blockConstraints058, DerivationConstraint.evaluate, x,
        blockVariables058, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA058 blockB058
    blockLeftInverse058 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![0, -2, 2, 1]
  · obtain ⟨q, hq'⟩ := (blockSupport058 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables059 : Fin 1 → Fin 26 × Fin 26 :=
  ![(8, 17)]
private def blockConstraints059 : Fin 1 → DerivationConstraint :=
  ![.entry 2 0 17]
private def blockA059 : Matrix (Fin 1) (Fin 1) (ZMod 2) :=
  ![![1]]
private def blockB059 : Matrix (Fin 1) (Fin 1) (ZMod 2) :=
  ![![1]]

private theorem blockLeftInverse059 : blockB059 * blockA059 = 1 := by
  decide +kernel

private theorem blockSupport059 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![0, -2, 2, 2] k) ↔ ∃ q, blockVariables059 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 59, a nonroot degree with 1 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock059 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, -2, 2, 2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 1) : (blockConstraints059 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 1 → R := fun q => X (blockVariables059 q).1 (blockVariables059 q).2
  have hx : blockA059.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA059 r i) * x i = 0
    have h := hc r
    fin_cases r; simp [blockA059, blockConstraints059, DerivationConstraint.evaluate, x,
        blockVariables059, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA059 blockB059
    blockLeftInverse059 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![0, -2, 2, 2]
  · obtain ⟨q, hq'⟩ := (blockSupport059 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables060 : Fin 2 → Fin 26 × Fin 26 :=
  ![(11, 2), (23, 14)]
private def blockConstraints060 : Fin 2 → DerivationConstraint :=
  ![.entry 0 8 14, .entry 0 11 17]
private def blockA060 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]
private def blockB060 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]

private theorem blockLeftInverse060 : blockB060 * blockA060 = 1 := by
  decide +kernel

private theorem blockSupport060 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![0, -2, 3, -1] k) ↔ ∃ q, blockVariables060 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 60, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock060 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, -2, 3, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints060 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables060 q).1 (blockVariables060 q).2
  have hx : blockA060.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA060 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA060, blockConstraints060, DerivationConstraint.evaluate, x,
        blockVariables060, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA060 blockB060
    blockLeftInverse060 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![0, -2, 3, -1]
  · obtain ⟨q, hq'⟩ := (blockSupport060 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables061 : Fin 2 → Fin 26 × Fin 26 :=
  ![(8, 14), (11, 17)]
private def blockConstraints061 : Fin 2 → DerivationConstraint :=
  ![.entry 2 0 14, .entry 2 1 17]
private def blockA061 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 0], ![0, 1]]
private def blockB061 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 0], ![0, 1]]

private theorem blockLeftInverse061 : blockB061 * blockA061 = 1 := by
  decide +kernel

private theorem blockSupport061 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![0, -2, 3, 0] k) ↔ ∃ q, blockVariables061 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 61, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock061 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, -2, 3, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints061 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables061 q).1 (blockVariables061 q).2
  have hx : blockA061.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA061 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA061, blockConstraints061, DerivationConstraint.evaluate, x,
        blockVariables061, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA061 blockB061
    blockLeftInverse061 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![0, -2, 3, 0]
  · obtain ⟨q, hq'⟩ := (blockSupport061 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables062 : Fin 1 → Fin 26 × Fin 26 :=
  ![(11, 14)]
private def blockConstraints062 : Fin 1 → DerivationConstraint :=
  ![.entry 2 1 14]
private def blockA062 : Matrix (Fin 1) (Fin 1) (ZMod 2) :=
  ![![1]]
private def blockB062 : Matrix (Fin 1) (Fin 1) (ZMod 2) :=
  ![![1]]

private theorem blockLeftInverse062 : blockB062 * blockA062 = 1 := by
  decide +kernel

private theorem blockSupport062 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![0, -2, 4, -2] k) ↔ ∃ q, blockVariables062 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 62, a nonroot degree with 1 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock062 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, -2, 4, -2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 1) : (blockConstraints062 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 1 → R := fun q => X (blockVariables062 q).1 (blockVariables062 q).2
  have hx : blockA062.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA062 r i) * x i = 0
    have h := hc r
    fin_cases r; simp [blockA062, blockConstraints062, DerivationConstraint.evaluate, x,
        blockVariables062, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA062 blockB062
    blockLeftInverse062 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![0, -2, 4, -2]
  · obtain ⟨q, hq'⟩ := (blockSupport062 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables063 : Fin 2 → Fin 26 × Fin 26 :=
  ![(23, 1), (24, 2)]
private def blockConstraints063 : Fin 2 → DerivationConstraint :=
  ![.entry 0 8 1, .entry 0 10 2]
private def blockA063 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 0], ![0, 1]]
private def blockB063 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 0], ![0, 1]]

private theorem blockLeftInverse063 : blockB063 * blockA063 = 1 := by
  decide +kernel

private theorem blockSupport063 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![0, -1, 0, 1] k) ↔ ∃ q, blockVariables063 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 63, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock063 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, -1, 0, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints063 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables063 q).1 (blockVariables063 q).2
  have hx : blockA063.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA063 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA063, blockConstraints063, DerivationConstraint.evaluate, x,
        blockVariables063, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA063 blockB063
    blockLeftInverse063 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![0, -1, 0, 1]
  · obtain ⟨q, hq'⟩ := (blockSupport063 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables064 : Fin 6 → Fin 26 × Fin 26 :=
  ![(8, 1), (10, 2), (16, 7), (18, 9), (23, 15), (24, 17)]
private def blockConstraints064 : Fin 6 → DerivationConstraint :=
  ![.entry 0 8 15, .entry 0 10 17, .entry 1 0 2, .entry 1 3 7, .entry 1 4 9, .quotient 21]
private def blockA064 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ![![1, 0, 0, 0, 1, 0], ![0, 1, 0, 0, 0, 1], ![1, 1, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0],
      ![1, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 0, 0]]
private def blockB064 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 1], ![0, 0, 1, 0, 0, 1], ![0, 0, 0, 1, 0, 1], ![0, 0, 0, 0, 1, 1],
      ![1, 0, 0, 0, 0, 1], ![0, 1, 1, 0, 0, 1]]

private theorem blockLeftInverse064 : blockB064 * blockA064 = 1 := by
  decide +kernel

private theorem blockSupport064 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![0, -1, 0, 2] k) ↔ ∃ q, blockVariables064 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 64, a root degree with 6 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock064 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, -1, 0, 2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 6) : (blockConstraints064 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 6 → R := fun q => X (blockVariables064 q).1 (blockVariables064 q).2
  have hx : blockA064.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA064 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA064, blockConstraints064, DerivationConstraint.evaluate, x,
        blockVariables064, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA064 blockB064
    blockLeftInverse064 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![0, -1, 0, 2]
  · obtain ⟨q, hq'⟩ := (blockSupport064 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables065 : Fin 2 → Fin 26 × Fin 26 :=
  ![(8, 15), (10, 17)]
private def blockConstraints065 : Fin 2 → DerivationConstraint :=
  ![.entry 1 0 17, .entry 1 8 25]
private def blockA065 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]
private def blockB065 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 0]]

private theorem blockLeftInverse065 : blockB065 * blockA065 = 1 := by
  decide +kernel

private theorem blockSupport065 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![0, -1, 0, 3] k) ↔ ∃ q, blockVariables065 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 65, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock065 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, -1, 0, 3] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints065 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables065 q).1 (blockVariables065 q).2
  have hx : blockA065.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA065 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA065, blockConstraints065, DerivationConstraint.evaluate, x,
        blockVariables065, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA065 blockB065
    blockLeftInverse065 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![0, -1, 0, 3]
  · obtain ⟨q, hq'⟩ := (blockSupport065 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables066 : Fin 2 → Fin 26 × Fin 26 :=
  ![(23, 0), (25, 2)]
private def blockConstraints066 : Fin 2 → DerivationConstraint :=
  ![.entry 0 11 1, .entry 0 12 2]
private def blockA066 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 0], ![0, 1]]
private def blockB066 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 0], ![0, 1]]

private theorem blockLeftInverse066 : blockB066 * blockA066 = 1 := by
  decide +kernel

private theorem blockSupport066 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![0, -1, 1, -1] k) ↔ ∃ q, blockVariables066 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 66, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock066 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, -1, 1, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints066 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables066 q).1 (blockVariables066 q).2
  have hx : blockA066.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA066 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA066, blockConstraints066, DerivationConstraint.evaluate, x,
        blockVariables066, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA066 blockB066
    blockLeftInverse066 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![0, -1, 1, -1]
  · obtain ⟨q, hq'⟩ := (blockSupport066 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables067 : Fin 12 → Fin 26 × Fin 26 :=
  ![(8, 0), (11, 1), (12, 2), (13, 2), (16, 5), (18, 6), (19, 7), (20, 9), (23, 12), (23, 13),
      (24, 14), (25, 17)]
private def blockConstraints067 : Fin 12 → DerivationConstraint :=
  ![.entry 0 0 2, .entry 0 3 7, .entry 0 4 9, .entry 0 8 12, .entry 0 8 13, .entry 0 10 14,
      .entry 0 11 15, .entry 0 12 17, .entry 0 16 21, .entry 0 18 22, .entry 1 1 2, .ideal 23]
private def blockA067 : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ![![1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
      ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
      ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      ![0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
private def blockB067 : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1],
      ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1],
      ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1], ![1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1]]

private theorem blockLeftInverse067 : blockB067 * blockA067 = 1 := by
  decide +kernel

private theorem blockSupport067 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![0, -1, 1, 0] k) ↔ ∃ q, blockVariables067 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 67, a root degree with 12 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock067 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, -1, 1, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 12) : (blockConstraints067 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 12 → R := fun q => X (blockVariables067 q).1 (blockVariables067 q).2
  have hx : blockA067.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA067 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA067, blockConstraints067, DerivationConstraint.evaluate, x,
        blockVariables067, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA067 blockB067
    blockLeftInverse067 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![0, -1, 1, 0]
  · obtain ⟨q, hq'⟩ := (blockSupport067 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables068 : Fin 12 → Fin 26 × Fin 26 :=
  ![(0, 2), (3, 7), (4, 9), (8, 12), (8, 13), (10, 14), (11, 15), (12, 17), (13, 17), (16, 21),
      (18, 22), (23, 25)]
private def blockConstraints068 : Fin 12 → DerivationConstraint :=
  ![.entry 0 0 17, .entry 0 8 25, .entry 1 0 14, .entry 1 1 17, .entry 1 3 21, .entry 1 4 22,
      .entry 1 8 24, .entry 1 11 25, .entry 2 0 12, .entry 2 3 19, .entry 2 4 20, .ideal 8]
private def blockA068 : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ![![1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
      ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0],
      ![0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0],
      ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1],
      ![1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
private def blockB068 : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1],
      ![0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      ![0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1], ![1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
      ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1],
      ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1], ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1]]

private theorem blockLeftInverse068 : blockB068 * blockA068 = 1 := by
  decide +kernel

private theorem blockSupport068 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![0, -1, 1, 1] k) ↔ ∃ q, blockVariables068 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 68, a root degree with 12 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock068 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, -1, 1, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 12) : (blockConstraints068 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 12 → R := fun q => X (blockVariables068 q).1 (blockVariables068 q).2
  have hx : blockA068.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA068 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA068, blockConstraints068, DerivationConstraint.evaluate, x,
        blockVariables068, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA068 blockB068
    blockLeftInverse068 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![0, -1, 1, 1]
  · obtain ⟨q, hq'⟩ := (blockSupport068 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd

private def blockVariables069 : Fin 2 → Fin 26 × Fin 26 :=
  ![(0, 17), (8, 25)]
private def blockConstraints069 : Fin 2 → DerivationConstraint :=
  ![.entry 2 0 25, .entry 7 0 22]
private def blockA069 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![1, 1], ![1, 0]]
private def blockB069 : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![![0, 1], ![1, 1]]

private theorem blockLeftInverse069 : blockB069 * blockA069 = 1 := by
  decide +kernel

private theorem blockSupport069 (i j : Fin 26) :
    (∀ k, entryDegree i j k = ![0, -1, 1, 2] k) ↔ ∃ q, blockVariables069 q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 69, a nonroot degree with 2 supported matrix entries, has trivial
kernel after imposing the derivation and coordinate equations. -/
theorem eq_zero_of_gradeBlock069 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, -1, 1, 2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  have hc (r : Fin 2) : (blockConstraints069 r).evaluate X = 0 :=
    DerivationConstraint.evaluate_eq_zero hX hq hi _
  let x : Fin 2 → R := fun q => X (blockVariables069 q).1 (blockVariables069 q).2
  have hx : blockA069.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ i, ZMod.castHom dvd_rfl R (blockA069 r i) * x i = 0
    have h := hc r
    fin_cases r <;> simp [blockA069, blockConstraints069, DerivationConstraint.evaluate, x,
        blockVariables069, Fin.sum_univ_succ, multTargetOne, multCoeffOne, multTargetTwo,
        multCoeffTwo, multRowTargetOne, multRowCoeffOne, multRowTargetTwo, multRowCoeffTwo,
        multIndexOne, multIndexCoeffOne, multIndexTwo, multIndexCoeffTwo, coordinateCoeff,
        coordinateRow, coordinateCol, idealRow, idealCol] at h ⊢
    all_goals grind
  have hx0 := eq_zero_of_modTwo_leftInverse blockA069 blockB069
    blockLeftInverse069 x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = ![0, -1, 1, 2]
  · obtain ⟨q, hq'⟩ := (blockSupport069 i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd


end TauCeti.F4ShortRoot
