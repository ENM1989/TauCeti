/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.IdealCoordinate

/-!
# Rows 24 to 25 of a derivation with vanishing coordinates

A matrix differentiating the invariant symmetric multiplication of the twenty-six-dimensional
module of type `F₄` modulo two, and annihilated by the twenty-six short-root quotient coordinates
and by the twenty-six ideal coordinates, is zero. This file proves that for the entries in rows
24 to 25.

The derivation equations are graded by the weight of the entry they constrain, so each entry is
determined by the few equations of its own weight together with the vanishing coordinates of that
weight; the proof of each entry is that combination. The equations themselves are the entrywise
form `TauCeti.F4ShortRoot.IsDerivation.entry` of the derivation equations, instantiated at the
relevant indices, and each combination is exact up to multiples of two, which vanish in
characteristic two.

## Main results

* `TauCeti.F4ShortRoot.entry_row_24` and its companions up to
  `TauCeti.F4ShortRoot.entry_row_25`: the entries of these rows vanish.
-/

public section

open Matrix

namespace TauCeti.F4ShortRoot

universe u

variable {R : Type u} [CommRing R] [CharP R 2]

/-- Every entry of the `24`th row of a derivation all of whose coordinates vanish
is zero. -/
theorem entry_row_24 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hq : ∀ p, quotientCoordinate p X = 0) (hi : ∀ a, X (idealRow a) (idealCol a) = 0)
    (n : Fin 26) : X 24 n = 0 := by
  have htwo : (2 : R) = 0 := by exact_mod_cast CharP.cast_eq_zero R 2
  have hc := quotientCoordinate_entries hq
  have d0_13_1 : X 13 0 * ((0 : ℤ) : R) + X 13 0 * ((0 : ℤ) : R) -
        (((2 : ℤ) : R) * X 25 1 + ((0 : ℤ) : R) * X 0 1) =
      ((1 : ℤ) : R) * X 24 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 13 1
  have d0_10_1 : X 10 0 * ((0 : ℤ) : R) + X 10 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 24 1 + ((0 : ℤ) : R) * X 0 1) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 10 1
  have d0_10_2 : X 10 0 * ((0 : ℤ) : R) + X 10 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 24 2 + ((0 : ℤ) : R) * X 0 2) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 10 2
  have d0_10_3 : X 10 0 * ((0 : ℤ) : R) + X 10 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 24 3 + ((0 : ℤ) : R) * X 0 3) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 10 3
  have d0_10_4 : X 10 0 * ((0 : ℤ) : R) + X 10 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 24 4 + ((0 : ℤ) : R) * X 0 4) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 10 4
  have c25 : ((1 : ℤ) : R) * X 18 0 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 25
  have d0_10_5 : X 10 0 * ((0 : ℤ) : R) + X 10 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 24 5 + ((0 : ℤ) : R) * X 0 5) =
      ((-3 : ℤ) : R) * X 18 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 10 5
  have c24 : ((1 : ℤ) : R) * X 16 0 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 24
  have d0_10_6 : X 10 0 * ((0 : ℤ) : R) + X 10 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 24 6 + ((0 : ℤ) : R) * X 0 6) =
      ((3 : ℤ) : R) * X 16 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 10 6
  have d0_10_7 : X 10 0 * ((0 : ℤ) : R) + X 10 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 24 7 + ((0 : ℤ) : R) * X 0 7) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 10 7
  have c23 : ((1 : ℤ) : R) * X 14 0 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 23
  have d0_10_8 : X 10 0 * ((0 : ℤ) : R) + X 10 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 24 8 + ((0 : ℤ) : R) * X 0 8) =
      ((-3 : ℤ) : R) * X 14 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 10 8
  have d0_10_9 : X 10 0 * ((0 : ℤ) : R) + X 10 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 24 9 + ((0 : ℤ) : R) * X 0 9) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 10 9
  have d0_10_10 : X 10 0 * ((0 : ℤ) : R) + X 10 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 24 10 + ((0 : ℤ) : R) * X 0 10) =
      ((3 : ℤ) : R) * X 12 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 10 10
  have i25 : X 12 0 = 0 := hi 25
  have d0_10_11 : X 10 0 * ((0 : ℤ) : R) + X 10 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 24 11 + ((0 : ℤ) : R) * X 0 11) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 10 11
  have d0_10_12 : X 10 0 * ((0 : ℤ) : R) + X 10 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 24 12 + ((0 : ℤ) : R) * X 0 12) =
      ((3 : ℤ) : R) * X 10 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 10 12
  have i24 : X 10 0 = 0 := hi 24
  have d0_10_13 : X 10 0 * ((3 : ℤ) : R) + X 10 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 24 13 + ((0 : ℤ) : R) * X 0 13) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 10 13
  have d0_10_14 : X 10 0 * ((0 : ℤ) : R) + X 10 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 24 14 + ((0 : ℤ) : R) * X 0 14) =
      ((-3 : ℤ) : R) * X 8 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 10 14
  have i23 : X 8 0 = 0 := hi 23
  have d1_12_15 : X 12 0 * ((0 : ℤ) : R) + X 12 0 * ((0 : ℤ) : R) -
        (((1 : ℤ) : R) * X 24 15 + ((0 : ℤ) : R) * X 0 15) =
      ((-2 : ℤ) : R) * X 10 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 12 15
  have d0_10_16 : X 10 0 * ((0 : ℤ) : R) + X 10 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 24 16 + ((0 : ℤ) : R) * X 0 16) =
      ((3 : ℤ) : R) * X 6 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 10 16
  have i22 : X 6 0 = 0 := hi 22
  have c21 : ((1 : ℤ) : R) * X 8 1 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 21
  have d0_10_17 : X 10 2 * ((3 : ℤ) : R) + X 10 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 24 17 + ((0 : ℤ) : R) * X 0 17) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 10 17
  have d1_0_2 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 10 2 + ((0 : ℤ) : R) * X 0 2) =
      ((3 : ℤ) : R) * X 8 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 0 2
  have d0_10_18 : X 10 0 * ((0 : ℤ) : R) + X 10 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 24 18 + ((0 : ℤ) : R) * X 0 18) =
      ((-3 : ℤ) : R) * X 5 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 10 18
  have i21 : X 5 0 = 0 := hi 21
  have c19 : ((1 : ℤ) : R) * X 6 1 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 19
  have d0_10_19 : X 10 3 * ((3 : ℤ) : R) + X 10 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 24 19 + ((0 : ℤ) : R) * X 0 19) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 10 19
  have d1_0_3 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 10 3 + ((0 : ℤ) : R) * X 0 3) =
      ((-3 : ℤ) : R) * X 6 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 0 3
  have c16 : ((1 : ℤ) : R) * X 5 1 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 16
  have d0_10_20 : X 10 4 * ((3 : ℤ) : R) + X 10 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 24 20 + ((0 : ℤ) : R) * X 0 20) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 10 20
  have d1_0_4 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 10 4 + ((0 : ℤ) : R) * X 0 4) =
      ((3 : ℤ) : R) * X 5 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 0 4
  have d0_10_21 : X 10 5 * ((3 : ℤ) : R) + X 10 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 24 21 + ((0 : ℤ) : R) * X 0 21) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 10 21
  have d1_0_5 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 10 5 + ((0 : ℤ) : R) * X 0 5) =
      ((3 : ℤ) : R) * X 4 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 0 5
  have i18 : X 4 1 = 0 := hi 18
  have d0_10_22 : X 10 6 * ((3 : ℤ) : R) + X 10 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 24 22 + ((0 : ℤ) : R) * X 0 22) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 10 22
  have d1_0_6 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 10 6 + ((0 : ℤ) : R) * X 0 6) =
      ((-3 : ℤ) : R) * X 3 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 0 6
  have i16 : X 3 1 = 0 := hi 16
  have d0_10_23 : X 10 8 * ((3 : ℤ) : R) + X 10 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 24 23 + ((0 : ℤ) : R) * X 0 23) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 10 23
  have d1_0_8 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 10 8 + ((0 : ℤ) : R) * X 0 8) =
      ((3 : ℤ) : R) * X 2 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 0 8
  have i14 : X 2 1 = 0 := hi 14
  have d0_10_24 : X 10 10 * ((3 : ℤ) : R) + X 10 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 24 24 + ((0 : ℤ) : R) * X 0 24) =
      ((3 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 10 24
  have i12 : X 10 10 = 0 := hi 12
  have i13 : X 0 0 = 0 := hi 13
  have d0_10_25 : X 10 12 * ((-1 : ℤ) : R) + X 10 13 * ((2 : ℤ) : R) -
        (((3 : ℤ) : R) * X 24 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 10 25
  have d1_0_12 : X 0 1 * ((-3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 10 12 + ((0 : ℤ) : R) * X 0 12) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 0 12
  have i10 : X 0 1 = 0 := hi 10
  fin_cases n
  · exact (show X 24 0 = 0 by
      linear_combination d0_13_1 + ((1 : R) * X 24 0) * htwo + ((1 : R) * X 25 1) * htwo)
  · exact (show X 24 1 = 0 by linear_combination d0_10_1 + ((2 : R) * X 24 1) * htwo)
  · exact (show X 24 2 = 0 by linear_combination d0_10_2 + ((2 : R) * X 24 2) * htwo)
  · exact (show X 24 3 = 0 by linear_combination d0_10_3 + ((2 : R) * X 24 3) * htwo)
  · exact (show X 24 4 = 0 by linear_combination d0_10_4 + ((2 : R) * X 24 4) * htwo)
  · exact (show X 24 5 = 0 by
      linear_combination c25 + d0_10_5 + ((-2 : R) * X 18 0) * htwo + ((2 : R) * X 24 5) * htwo)
  · exact (show X 24 6 = 0 by
      linear_combination c24 + d0_10_6 + ((1 : R) * X 16 0) * htwo + ((2 : R) * X 24 6) * htwo)
  · exact (show X 24 7 = 0 by linear_combination d0_10_7 + ((2 : R) * X 24 7) * htwo)
  · exact (show X 24 8 = 0 by
      linear_combination c23 + d0_10_8 + ((-2 : R) * X 14 0) * htwo + ((2 : R) * X 24 8) * htwo)
  · exact (show X 24 9 = 0 by linear_combination d0_10_9 + ((2 : R) * X 24 9) * htwo)
  · exact (show X 24 10 = 0 by
      linear_combination d0_10_10 + i25 + ((1 : R) * X 12 0) * htwo +
        ((2 : R) * X 24 10) * htwo)
  · exact (show X 24 11 = 0 by linear_combination d0_10_11 + ((2 : R) * X 24 11) * htwo)
  · exact (show X 24 12 = 0 by
      linear_combination d0_10_12 + i24 + ((1 : R) * X 10 0) * htwo +
        ((2 : R) * X 24 12) * htwo)
  · exact (show X 24 13 = 0 by
      linear_combination d0_10_13 + i24 + ((-2 : R) * X 10 0) * htwo +
        ((2 : R) * X 24 13) * htwo)
  · exact (show X 24 14 = 0 by
      linear_combination d0_10_14 + i23 + ((-2 : R) * X 8 0) * htwo +
        ((2 : R) * X 24 14) * htwo)
  · exact (show X 24 15 = 0 by
      linear_combination d1_12_15 + ((-1 : R) * X 10 1) * htwo + ((1 : R) * X 24 15) * htwo)
  · exact (show X 24 16 = 0 by
      linear_combination d0_10_16 + i22 + ((1 : R) * X 6 0) * htwo + ((2 : R) * X 24 16) * htwo)
  · exact (show X 24 17 = 0 by
      linear_combination c21 + d0_10_17 + d1_0_2 + ((1 : R) * X 8 1) * htwo +
        ((-3 : R) * X 10 2) * htwo + ((2 : R) * X 24 17) * htwo)
  · exact (show X 24 18 = 0 by
      linear_combination d0_10_18 + i21 + ((-2 : R) * X 5 0) * htwo +
        ((2 : R) * X 24 18) * htwo)
  · exact (show X 24 19 = 0 by
      linear_combination c19 + d0_10_19 + d1_0_3 + ((-2 : R) * X 6 1) * htwo +
        ((-3 : R) * X 10 3) * htwo + ((2 : R) * X 24 19) * htwo)
  · exact (show X 24 20 = 0 by
      linear_combination c16 + d0_10_20 + d1_0_4 + ((1 : R) * X 5 1) * htwo +
        ((-3 : R) * X 10 4) * htwo + ((2 : R) * X 24 20) * htwo)
  · exact (show X 24 21 = 0 by
      linear_combination d0_10_21 + d1_0_5 + i18 + ((1 : R) * X 4 1) * htwo +
        ((-3 : R) * X 10 5) * htwo + ((2 : R) * X 24 21) * htwo)
  · exact (show X 24 22 = 0 by
      linear_combination d0_10_22 + d1_0_6 + i16 + ((-2 : R) * X 3 1) * htwo +
        ((-3 : R) * X 10 6) * htwo + ((2 : R) * X 24 22) * htwo)
  · exact (show X 24 23 = 0 by
      linear_combination d0_10_23 + d1_0_8 + i14 + ((1 : R) * X 2 1) * htwo +
        ((-3 : R) * X 10 8) * htwo + ((2 : R) * X 24 23) * htwo)
  · exact (show X 24 24 = 0 by
      linear_combination d0_10_24 + i12 + i13 + ((1 : R) * X 0 0) * htwo +
        ((-2 : R) * X 10 10) * htwo + ((2 : R) * X 24 24) * htwo)
  · exact (show X 24 25 = 0 by
      linear_combination d0_10_25 + d1_0_12 + i10 + ((1 : R) * X 0 1) * htwo +
        ((-1 : R) * X 10 12) * htwo + ((-1 : R) * X 10 13) * htwo + ((2 : R) * X 24 25) * htwo)

/-- Every entry of the `25`th row of a derivation all of whose coordinates vanish
is zero. -/
theorem entry_row_25 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hq : ∀ p, quotientCoordinate p X = 0) (hi : ∀ a, X (idealRow a) (idealCol a) = 0)
    (n : Fin 26) : X 25 n = 0 := by
  have htwo : (2 : R) = 0 := by exact_mod_cast CharP.cast_eq_zero R 2
  have hc := quotientCoordinate_entries hq
  have d0_15_1 : X 15 0 * ((0 : ℤ) : R) + X 15 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1) =
      ((3 : ℤ) : R) * X 25 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 15 1
  have d1_17_2 : X 17 0 * ((0 : ℤ) : R) + X 17 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2) =
      ((3 : ℤ) : R) * X 25 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 17 2
  have d0_12_2 : X 12 0 * ((0 : ℤ) : R) + X 12 0 * ((0 : ℤ) : R) -
        (((-1 : ℤ) : R) * X 25 2 + ((0 : ℤ) : R) * X 0 2) =
      ((2 : ℤ) : R) * X 23 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 12 2
  have d0_12_3 : X 12 0 * ((0 : ℤ) : R) + X 12 0 * ((0 : ℤ) : R) -
        (((-1 : ℤ) : R) * X 25 3 + ((0 : ℤ) : R) * X 0 3) =
      ((-2 : ℤ) : R) * X 22 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 12 3
  have d0_12_4 : X 12 0 * ((0 : ℤ) : R) + X 12 0 * ((0 : ℤ) : R) -
        (((-1 : ℤ) : R) * X 25 4 + ((0 : ℤ) : R) * X 0 4) =
      ((2 : ℤ) : R) * X 21 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 12 4
  have d1_15_5 : X 15 0 * ((0 : ℤ) : R) + X 15 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 25 5 + ((0 : ℤ) : R) * X 0 5) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 15 5
  have d1_15_6 : X 15 0 * ((0 : ℤ) : R) + X 15 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 25 6 + ((0 : ℤ) : R) * X 0 6) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 15 6
  have c25 : ((1 : ℤ) : R) * X 18 0 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 25
  have d0_12_7 : X 12 0 * ((0 : ℤ) : R) + X 12 0 * ((0 : ℤ) : R) -
        (((-1 : ℤ) : R) * X 25 7 + ((0 : ℤ) : R) * X 0 7) =
      ((1 : ℤ) : R) * X 18 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 12 7
  have d1_15_8 : X 15 0 * ((0 : ℤ) : R) + X 15 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 25 8 + ((0 : ℤ) : R) * X 0 8) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 15 8
  have c24 : ((1 : ℤ) : R) * X 16 0 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 24
  have d0_12_9 : X 12 0 * ((0 : ℤ) : R) + X 12 0 * ((0 : ℤ) : R) -
        (((-1 : ℤ) : R) * X 25 9 + ((0 : ℤ) : R) * X 0 9) =
      ((-1 : ℤ) : R) * X 16 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 12 9
  have d0_12_10 : X 12 0 * ((0 : ℤ) : R) + X 12 0 * ((0 : ℤ) : R) -
        (((-1 : ℤ) : R) * X 25 10 + ((0 : ℤ) : R) * X 0 10) =
      ((-2 : ℤ) : R) * X 15 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 12 10
  have c23 : ((1 : ℤ) : R) * X 14 0 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 23
  have d0_12_11 : X 12 0 * ((0 : ℤ) : R) + X 12 0 * ((0 : ℤ) : R) -
        (((-1 : ℤ) : R) * X 25 11 + ((0 : ℤ) : R) * X 0 11) =
      ((1 : ℤ) : R) * X 14 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 12 11
  have d0_12_12 : X 12 0 * ((0 : ℤ) : R) + X 12 0 * ((0 : ℤ) : R) -
        (((-1 : ℤ) : R) * X 25 12 + ((0 : ℤ) : R) * X 0 12) =
      ((-2 : ℤ) : R) * X 12 0 + ((2 : ℤ) : R) * X 13 0 :=
    hX.entry 0 12 12
  have d0_12_13 : X 12 0 * ((3 : ℤ) : R) + X 12 0 * ((0 : ℤ) : R) -
        (((-1 : ℤ) : R) * X 25 13 + ((0 : ℤ) : R) * X 0 13) =
      ((2 : ℤ) : R) * X 12 0 + ((4 : ℤ) : R) * X 13 0 :=
    hX.entry 0 12 13
  have i25 : X 12 0 = 0 := hi 25
  have c22 : ((1 : ℤ) : R) * X 11 0 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 22
  have d0_12_14 : X 12 0 * ((0 : ℤ) : R) + X 12 0 * ((0 : ℤ) : R) -
        (((-1 : ℤ) : R) * X 25 14 + ((0 : ℤ) : R) * X 0 14) =
      ((1 : ℤ) : R) * X 11 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 12 14
  have d0_12_15 : X 12 1 * ((3 : ℤ) : R) + X 12 0 * ((0 : ℤ) : R) -
        (((-1 : ℤ) : R) * X 25 15 + ((0 : ℤ) : R) * X 0 15) =
      ((-2 : ℤ) : R) * X 10 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 12 15
  have d0_14_17 : X 14 2 * ((3 : ℤ) : R) + X 14 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 17 + ((0 : ℤ) : R) * X 0 17) =
      ((-3 : ℤ) : R) * X 10 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 14 17
  have d1_2_2 : X 2 0 * ((0 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 14 2 + ((0 : ℤ) : R) * X 0 2) =
      ((3 : ℤ) : R) * X 12 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 2 2
  have i24 : X 10 0 = 0 := hi 24
  have c20 : ((1 : ℤ) : R) * X 9 0 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 20
  have d0_12_16 : X 12 0 * ((0 : ℤ) : R) + X 12 0 * ((0 : ℤ) : R) -
        (((-1 : ℤ) : R) * X 25 16 + ((0 : ℤ) : R) * X 0 16) =
      ((-1 : ℤ) : R) * X 9 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 12 16
  have d0_11_15 : X 11 1 * ((3 : ℤ) : R) + X 11 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 15 + ((0 : ℤ) : R) * X 0 15) =
      ((-3 : ℤ) : R) * X 8 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 11 15
  have d1_15_17 : X 15 0 * ((0 : ℤ) : R) + X 15 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 25 17 + ((0 : ℤ) : R) * X 0 17) =
      ((-3 : ℤ) : R) * X 11 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 15 17
  have i23 : X 8 0 = 0 := hi 23
  have c18 : ((1 : ℤ) : R) * X 7 0 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 18
  have d0_12_18 : X 12 0 * ((0 : ℤ) : R) + X 12 0 * ((0 : ℤ) : R) -
        (((-1 : ℤ) : R) * X 25 18 + ((0 : ℤ) : R) * X 0 18) =
      ((1 : ℤ) : R) * X 7 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 12 18
  have d0_9_15 : X 9 1 * ((3 : ℤ) : R) + X 9 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 15 + ((0 : ℤ) : R) * X 0 15) =
      ((-3 : ℤ) : R) * X 6 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 9 15
  have d1_15_19 : X 15 0 * ((0 : ℤ) : R) + X 15 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 25 19 + ((0 : ℤ) : R) * X 0 19) =
      ((3 : ℤ) : R) * X 9 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 15 19
  have i22 : X 6 0 = 0 := hi 22
  have d0_7_15 : X 7 1 * ((3 : ℤ) : R) + X 7 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 15 + ((0 : ℤ) : R) * X 0 15) =
      ((-3 : ℤ) : R) * X 5 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 7 15
  have d1_15_20 : X 15 0 * ((0 : ℤ) : R) + X 15 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 25 20 + ((0 : ℤ) : R) * X 0 20) =
      ((-3 : ℤ) : R) * X 7 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 15 20
  have i21 : X 5 0 = 0 := hi 21
  have d0_0_5 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 13 5 + ((0 : ℤ) : R) * X 0 5) =
      ((3 : ℤ) : R) * X 4 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 0 5
  have d0_12_21 : X 12 5 * ((3 : ℤ) : R) + X 12 0 * ((0 : ℤ) : R) -
        (((-1 : ℤ) : R) * X 25 21 + ((0 : ℤ) : R) * X 0 21) =
      ((2 : ℤ) : R) * X 4 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 12 21
  have d1_1_5 : X 1 0 * ((0 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 12 5 + ((-3 : ℤ) : R) * X 13 5) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 1 5
  have i20 : X 4 0 = 0 := hi 20
  have d0_0_6 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 13 6 + ((0 : ℤ) : R) * X 0 6) =
      ((-3 : ℤ) : R) * X 3 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 0 6
  have d0_12_22 : X 12 6 * ((3 : ℤ) : R) + X 12 0 * ((0 : ℤ) : R) -
        (((-1 : ℤ) : R) * X 25 22 + ((0 : ℤ) : R) * X 0 22) =
      ((-2 : ℤ) : R) * X 3 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 12 22
  have d1_1_6 : X 1 0 * ((0 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 12 6 + ((-3 : ℤ) : R) * X 13 6) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 1 6
  have i19 : X 3 0 = 0 := hi 19
  have d0_0_8 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 13 8 + ((0 : ℤ) : R) * X 0 8) =
      ((3 : ℤ) : R) * X 2 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 0 8
  have d0_12_23 : X 12 8 * ((3 : ℤ) : R) + X 12 0 * ((0 : ℤ) : R) -
        (((-1 : ℤ) : R) * X 25 23 + ((0 : ℤ) : R) * X 0 23) =
      ((2 : ℤ) : R) * X 2 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 12 23
  have d1_1_8 : X 1 0 * ((0 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 12 8 + ((-3 : ℤ) : R) * X 13 8) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 1 8
  have i17 : X 2 0 = 0 := hi 17
  have d0_2_14 : X 2 0 * ((0 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 17 14 + ((0 : ℤ) : R) * X 0 14) =
      ((-3 : ℤ) : R) * X 1 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 2 14
  have d2_17_24 : X 17 14 * ((3 : ℤ) : R) + X 17 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 25 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 17 24
  have i15 : X 1 0 = 0 := hi 15
  have d0_12_25 : X 12 12 * ((-1 : ℤ) : R) + X 12 13 * ((2 : ℤ) : R) -
        (((-1 : ℤ) : R) * X 25 25 + ((0 : ℤ) : R) * X 0 25) =
      ((-1 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 12 25
  have d2_2_12 : X 2 2 * ((3 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 12 12 + ((0 : ℤ) : R) * X 0 12) =
      ((3 : ℤ) : R) * X 2 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 2 12
  have i13 : X 0 0 = 0 := hi 13
  fin_cases n
  · exact (show X 25 0 = 0 by linear_combination d0_15_1 + ((2 : R) * X 25 0) * htwo)
  · exact (show X 25 1 = 0 by linear_combination d1_17_2 + ((2 : R) * X 25 1) * htwo)
  · exact (show X 25 2 = 0 by linear_combination d0_12_2 + ((1 : R) * X 23 0) * htwo)
  · exact (show X 25 3 = 0 by linear_combination d0_12_3 + ((-1 : R) * X 22 0) * htwo)
  · exact (show X 25 4 = 0 by linear_combination d0_12_4 + ((1 : R) * X 21 0) * htwo)
  · exact (show X 25 5 = 0 by linear_combination d1_15_5 + ((2 : R) * X 25 5) * htwo)
  · exact (show X 25 6 = 0 by linear_combination d1_15_6 + ((2 : R) * X 25 6) * htwo)
  · exact (show X 25 7 = 0 by linear_combination c25 + d0_12_7)
  · exact (show X 25 8 = 0 by linear_combination d1_15_8 + ((2 : R) * X 25 8) * htwo)
  · exact (show X 25 9 = 0 by linear_combination c24 + d0_12_9 + ((-1 : R) * X 16 0) * htwo)
  · exact (show X 25 10 = 0 by linear_combination d0_12_10 + ((-1 : R) * X 15 0) * htwo)
  · exact (show X 25 11 = 0 by linear_combination c23 + d0_12_11)
  · exact (show X 25 12 = 0 by
      linear_combination d0_12_12 + ((-1 : R) * X 12 0) * htwo + ((1 : R) * X 13 0) * htwo)
  · exact (show X 25 13 = 0 by
      linear_combination d0_12_13 + i25 + ((-1 : R) * X 12 0) * htwo +
        ((2 : R) * X 13 0) * htwo)
  · exact (show X 25 14 = 0 by linear_combination c22 + d0_12_14)
  · exact (show X 25 15 = 0 by
      linear_combination d0_12_15 + d0_14_17 + d1_2_2 + i24 + ((-3 : R) * X 10 0) * htwo +
        ((-3 : R) * X 14 2) * htwo)
  · exact (show X 25 16 = 0 by linear_combination c20 + d0_12_16 + ((-1 : R) * X 9 0) * htwo)
  · exact (show X 25 17 = 0 by
      linear_combination d0_11_15 + d1_15_17 + i23 + ((-2 : R) * X 8 0) * htwo +
        ((-3 : R) * X 11 1) * htwo + ((2 : R) * X 25 17) * htwo)
  · exact (show X 25 18 = 0 by linear_combination c18 + d0_12_18)
  · exact (show X 25 19 = 0 by
      linear_combination d0_9_15 + d1_15_19 + i22 + ((-2 : R) * X 6 0) * htwo +
        ((2 : R) * X 25 19) * htwo)
  · exact (show X 25 20 = 0 by
      linear_combination d0_7_15 + d1_15_20 + i21 + ((-2 : R) * X 5 0) * htwo +
        ((-3 : R) * X 7 1) * htwo + ((2 : R) * X 25 20) * htwo)
  · exact (show X 25 21 = 0 by
      linear_combination d0_0_5 + d0_12_21 + d1_1_5 + i20 + ((2 : R) * X 4 0) * htwo +
        ((-3 : R) * X 12 5) * htwo)
  · exact (show X 25 22 = 0 by
      linear_combination d0_0_6 + d0_12_22 + d1_1_6 + i19 + ((-3 : R) * X 3 0) * htwo +
        ((-3 : R) * X 12 6) * htwo)
  · exact (show X 25 23 = 0 by
      linear_combination d0_0_8 + d0_12_23 + d1_1_8 + i17 + ((2 : R) * X 2 0) * htwo +
        ((-3 : R) * X 12 8) * htwo)
  · exact (show X 25 24 = 0 by
      linear_combination d0_2_14 + d2_17_24 + i15 + ((-2 : R) * X 1 0) * htwo +
        ((2 : R) * X 25 24) * htwo)
  · exact (show X 25 25 = 0 by
      linear_combination d0_12_25 + d2_2_12 + i13 + ((-1 : R) * X 0 0) * htwo +
        ((2 : R) * X 12 12) * htwo + ((-1 : R) * X 12 13) * htwo)

end TauCeti.F4ShortRoot
