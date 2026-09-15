/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.DerivationGrading
public import TauCeti.Algebra.Lie.F4.ShortRoot.IdealCoordinate

/-!
# Linear constraints on type-F4 derivations

This packages an entry of the derivation identity or one of the two coordinate systems as a
single linear equation. Homogeneous block certificates can therefore select equations as data.
-/

public section

namespace TauCeti.F4ShortRoot
universe u

/-- A selectable linear equation used in a homogeneous derivation block. -/
inductive DerivationConstraint where
  | entry (k i j : Fin 26)
  | quotient (p : Fin 26)
  | ideal (a : Fin 26)

/-- Evaluation of a selected constraint on a matrix. -/
@[expose] def DerivationConstraint.evaluate {R : Type u} [CommRing R]
    (c : DerivationConstraint) (X : Matrix (Fin 26) (Fin 26) R) : R :=
  match c with
  | .entry k i j =>
      X i (multTargetOne k j) * ((multCoeffOne k j : ℤ) : R) +
          X i (multTargetTwo k j) * ((multCoeffTwo k j : ℤ) : R) -
        (((multRowCoeffOne k i : ℤ) : R) * X (multRowTargetOne k i) j +
          ((multRowCoeffTwo k i : ℤ) : R) * X (multRowTargetTwo k i) j) -
      (((multIndexCoeffOne i j : ℤ) : R) * X (multIndexOne i j) k +
        ((multIndexCoeffTwo i j : ℤ) : R) * X (multIndexTwo i j) k)
  | .quotient p =>
      ((coordinateCoeff 0 p : ℤ) : R) * X (coordinateRow 0 p) (coordinateCol 0 p) +
        ((coordinateCoeff 1 p : ℤ) : R) * X (coordinateRow 1 p) (coordinateCol 1 p)
  | .ideal a => X (idealRow a) (idealCol a)

/-- Every selected constraint vanishes under the corresponding hypotheses. -/
theorem DerivationConstraint.evaluate_eq_zero {R : Type u} [CommRing R]
    {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hq : ∀ p, quotientCoordinate p X = 0) (hi : ∀ a, X (idealRow a) (idealCol a) = 0)
    (c : DerivationConstraint) : c.evaluate X = 0 := by
  cases c with
  | entry k i j =>
      rw [DerivationConstraint.evaluate, sub_eq_zero]
      exact hX.entry k i j
  | quotient p =>
      exact quotientCoordinate_entries hq p
  | ideal a => exact hi a

end TauCeti.F4ShortRoot
