/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.IdealCoordinate

/-!
# Rows 10 to 13 of a derivation with vanishing coordinates

A matrix differentiating the invariant symmetric multiplication of the twenty-six-dimensional
module of type `F₄` modulo two, and annihilated by the twenty-six short-root quotient coordinates
and by the twenty-six ideal coordinates, is zero. This file proves that for the entries in rows
10 to 13.

The derivation equations are graded by the weight of the entry they constrain, so each entry is
determined by the few equations of its own weight together with the vanishing coordinates of that
weight; the proof of each entry is that combination. The equations themselves are the entrywise
form `TauCeti.F4ShortRoot.IsDerivation.entry` of the derivation equations, instantiated at the
relevant indices, and each combination is exact up to multiples of two, which vanish in
characteristic two.

## Main results

* `TauCeti.F4ShortRoot.entry_row_10` and its companions up to
  `TauCeti.F4ShortRoot.entry_row_13`: the entries of these rows vanish.
-/

public section

open Matrix

namespace TauCeti.F4ShortRoot

universe u

variable {R : Type u} [CommRing R] [CharP R 2]

/-- Every entry of the `10`th row of a derivation all of whose coordinates vanish
is zero. -/
theorem entry_row_10 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hq : ∀ p, quotientCoordinate p X = 0) (hi : ∀ a, X (idealRow a) (idealCol a) = 0)
    (n : Fin 26) : X 10 n = 0 := by
  have htwo : (2 : R) = 0 := by exact_mod_cast CharP.cast_eq_zero R 2
  have hc := quotientCoordinate_entries hq
  have i24 : X 10 0 = 0 := hi 24
  have d1_5_7 : X 5 0 * ((0 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 7 + ((0 : ℤ) : R) * X 0 7) =
      ((3 : ℤ) : R) * X 10 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 5 7
  have c21 : ((1 : ℤ) : R) * X 8 1 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 21
  have d1_0_2 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 10 2 + ((0 : ℤ) : R) * X 0 2) =
      ((3 : ℤ) : R) * X 8 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 0 2
  have c19 : ((1 : ℤ) : R) * X 6 1 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 19
  have d1_0_3 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 10 3 + ((0 : ℤ) : R) * X 0 3) =
      ((-3 : ℤ) : R) * X 6 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 0 3
  have c16 : ((1 : ℤ) : R) * X 5 1 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 16
  have d1_0_4 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 10 4 + ((0 : ℤ) : R) * X 0 4) =
      ((3 : ℤ) : R) * X 5 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 0 4
  have d1_0_5 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 10 5 + ((0 : ℤ) : R) * X 0 5) =
      ((3 : ℤ) : R) * X 4 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 0 5
  have i18 : X 4 1 = 0 := hi 18
  have d1_0_6 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 10 6 + ((0 : ℤ) : R) * X 0 6) =
      ((-3 : ℤ) : R) * X 3 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 0 6
  have i16 : X 3 1 = 0 := hi 16
  have d1_0_7 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 10 7 + ((0 : ℤ) : R) * X 0 7) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 0 7
  have d1_0_8 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 10 8 + ((0 : ℤ) : R) * X 0 8) =
      ((3 : ℤ) : R) * X 2 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 0 8
  have i14 : X 2 1 = 0 := hi 14
  have d1_0_9 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 10 9 + ((0 : ℤ) : R) * X 0 9) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 0 9
  have i12 : X 10 10 = 0 := hi 12
  have d1_0_11 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 10 11 + ((0 : ℤ) : R) * X 0 11) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 0 11
  have d1_0_12 : X 0 1 * ((-3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 10 12 + ((0 : ℤ) : R) * X 0 12) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 0 12
  have i10 : X 0 1 = 0 := hi 10
  have d1_0_13 : X 0 1 * ((-3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 10 13 + ((0 : ℤ) : R) * X 0 13) =
      ((3 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 0 13
  have d1_0_14 : X 0 2 * ((-3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 10 14 + ((0 : ℤ) : R) * X 0 14) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 0 14
  have i8 : X 0 2 = 0 := hi 8
  have d1_0_15 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 10 15 + ((0 : ℤ) : R) * X 0 15) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 0 15
  have d1_0_16 : X 0 3 * ((-3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 10 16 + ((0 : ℤ) : R) * X 0 16) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 0 16
  have i6 : X 0 3 = 0 := hi 6
  have d1_0_17 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 10 17 + ((0 : ℤ) : R) * X 0 17) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 0 17
  have d1_0_18 : X 0 4 * ((-3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 10 18 + ((0 : ℤ) : R) * X 0 18) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 0 18
  have i5 : X 0 4 = 0 := hi 5
  have d1_0_19 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 10 19 + ((0 : ℤ) : R) * X 0 19) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 0 19
  have d1_0_20 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 10 20 + ((0 : ℤ) : R) * X 0 20) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 0 20
  have c7 : ((1 : ℤ) : R) * X 0 7 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 7
  have d1_0_21 : X 0 7 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 10 21 + ((0 : ℤ) : R) * X 0 21) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 0 21
  have c5 : ((1 : ℤ) : R) * X 0 9 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 5
  have d1_0_22 : X 0 9 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 10 22 + ((0 : ℤ) : R) * X 0 22) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 0 22
  have c3 : ((1 : ℤ) : R) * X 0 11 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 3
  have d1_0_23 : X 0 11 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 10 23 + ((0 : ℤ) : R) * X 0 23) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 0 23
  have d4_0_21 : X 0 12 * ((2 : ℤ) : R) + X 0 13 * ((-1 : ℤ) : R) -
        (((3 : ℤ) : R) * X 5 21 + ((0 : ℤ) : R) * X 0 21) =
      ((0 : ℤ) : R) * X 0 4 + ((0 : ℤ) : R) * X 0 4 :=
    hX.entry 4 0 21
  have d7_5_24 : X 5 21 * ((-3 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 10 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 7 + ((0 : ℤ) : R) * X 0 7 :=
    hX.entry 7 5 24
  have i0 : X 0 13 = 0 := hi 0
  have d7_5_25 : X 5 0 * ((0 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 10 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 7 + ((0 : ℤ) : R) * X 0 7 :=
    hX.entry 7 5 25
  fin_cases n
  · exact (show X 10 0 = 0 by linear_combination i24)
  · exact (show X 10 1 = 0 by linear_combination d1_5_7 + ((2 : R) * X 10 1) * htwo)
  · exact (show X 10 2 = 0 by
      linear_combination c21 + d1_0_2 + ((1 : R) * X 8 1) * htwo + ((-1 : R) * X 10 2) * htwo)
  · exact (show X 10 3 = 0 by
      linear_combination c19 + d1_0_3 + ((-2 : R) * X 6 1) * htwo + ((-1 : R) * X 10 3) * htwo)
  · exact (show X 10 4 = 0 by
      linear_combination c16 + d1_0_4 + ((1 : R) * X 5 1) * htwo + ((-1 : R) * X 10 4) * htwo)
  · exact (show X 10 5 = 0 by
      linear_combination d1_0_5 + i18 + ((1 : R) * X 4 1) * htwo + ((-1 : R) * X 10 5) * htwo)
  · exact (show X 10 6 = 0 by
      linear_combination d1_0_6 + i16 + ((-2 : R) * X 3 1) * htwo + ((-1 : R) * X 10 6) * htwo)
  · exact (show X 10 7 = 0 by linear_combination d1_0_7 + ((-1 : R) * X 10 7) * htwo)
  · exact (show X 10 8 = 0 by
      linear_combination d1_0_8 + i14 + ((1 : R) * X 2 1) * htwo + ((-1 : R) * X 10 8) * htwo)
  · exact (show X 10 9 = 0 by linear_combination d1_0_9 + ((-1 : R) * X 10 9) * htwo)
  · exact (show X 10 10 = 0 by linear_combination i12)
  · exact (show X 10 11 = 0 by linear_combination d1_0_11 + ((-1 : R) * X 10 11) * htwo)
  · exact (show X 10 12 = 0 by
      linear_combination d1_0_12 + i10 + ((1 : R) * X 0 1) * htwo + ((-1 : R) * X 10 12) * htwo)
  · exact (show X 10 13 = 0 by
      linear_combination d1_0_13 + ((3 : R) * X 0 1) * htwo + ((-1 : R) * X 10 13) * htwo)
  · exact (show X 10 14 = 0 by
      linear_combination d1_0_14 + i8 + ((1 : R) * X 0 2) * htwo + ((-1 : R) * X 10 14) * htwo)
  · exact (show X 10 15 = 0 by linear_combination d1_0_15 + ((-1 : R) * X 10 15) * htwo)
  · exact (show X 10 16 = 0 by
      linear_combination d1_0_16 + i6 + ((1 : R) * X 0 3) * htwo + ((-1 : R) * X 10 16) * htwo)
  · exact (show X 10 17 = 0 by linear_combination d1_0_17 + ((-1 : R) * X 10 17) * htwo)
  · exact (show X 10 18 = 0 by
      linear_combination d1_0_18 + i5 + ((1 : R) * X 0 4) * htwo + ((-1 : R) * X 10 18) * htwo)
  · exact (show X 10 19 = 0 by linear_combination d1_0_19 + ((-1 : R) * X 10 19) * htwo)
  · exact (show X 10 20 = 0 by linear_combination d1_0_20 + ((-1 : R) * X 10 20) * htwo)
  · exact (show X 10 21 = 0 by
      linear_combination c7 + d1_0_21 + ((-2 : R) * X 0 7) * htwo + ((-1 : R) * X 10 21) * htwo)
  · exact (show X 10 22 = 0 by
      linear_combination c5 + d1_0_22 + ((-2 : R) * X 0 9) * htwo + ((-1 : R) * X 10 22) * htwo)
  · exact (show X 10 23 = 0 by
      linear_combination c3 + d1_0_23 + ((-2 : R) * X 0 11) * htwo +
        ((-1 : R) * X 10 23) * htwo)
  · exact (show X 10 24 = 0 by
      linear_combination d4_0_21 + d7_5_24 + i0 + ((-1 : R) * X 0 12) * htwo +
        ((3 : R) * X 5 21) * htwo + ((2 : R) * X 10 24) * htwo)
  · exact (show X 10 25 = 0 by linear_combination d7_5_25 + ((2 : R) * X 10 25) * htwo)

/-- Every entry of the `11`th row of a derivation all of whose coordinates vanish
is zero. -/
theorem entry_row_11 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hq : ∀ p, quotientCoordinate p X = 0) (hi : ∀ a, X (idealRow a) (idealCol a) = 0)
    (n : Fin 26) : X 11 n = 0 := by
  have htwo : (2 : R) = 0 := by exact_mod_cast CharP.cast_eq_zero R 2
  have hc := quotientCoordinate_entries hq
  have c22 : ((1 : ℤ) : R) * X 11 0 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 22
  have d0_11_15 : X 11 1 * ((3 : ℤ) : R) + X 11 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 15 + ((0 : ℤ) : R) * X 0 15) =
      ((-3 : ℤ) : R) * X 8 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 11 15
  have i23 : X 8 0 = 0 := hi 23
  have d0_11_17 : X 11 2 * ((3 : ℤ) : R) + X 11 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 17 + ((0 : ℤ) : R) * X 0 17) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 11 17
  have d0_11_19 : X 11 3 * ((3 : ℤ) : R) + X 11 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 19 + ((0 : ℤ) : R) * X 0 19) =
      ((3 : ℤ) : R) * X 4 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 11 19
  have i20 : X 4 0 = 0 := hi 20
  have d0_11_20 : X 11 4 * ((3 : ℤ) : R) + X 11 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 20 + ((0 : ℤ) : R) * X 0 20) =
      ((-3 : ℤ) : R) * X 3 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 11 20
  have i19 : X 3 0 = 0 := hi 19
  have d0_11_21 : X 11 5 * ((3 : ℤ) : R) + X 11 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 21 + ((0 : ℤ) : R) * X 0 21) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 11 21
  have d0_11_22 : X 11 6 * ((3 : ℤ) : R) + X 11 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 22 + ((0 : ℤ) : R) * X 0 22) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 11 22
  have c17 : ((1 : ℤ) : R) * X 4 2 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 17
  have d0_8_21 : X 8 5 * ((3 : ℤ) : R) + X 8 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 23 21 + ((0 : ℤ) : R) * X 0 21) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 8 21
  have d1_11_21 : X 11 7 * ((3 : ℤ) : R) + X 11 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 23 21 + ((0 : ℤ) : R) * X 0 21) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 11 21
  have d2_0_5 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 8 5 + ((0 : ℤ) : R) * X 0 5) =
      ((3 : ℤ) : R) * X 4 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 0 5
  have d0_11_23 : X 11 8 * ((3 : ℤ) : R) + X 11 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 23 + ((0 : ℤ) : R) * X 0 23) =
      ((3 : ℤ) : R) * X 1 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 11 23
  have i15 : X 1 0 = 0 := hi 15
  have c14 : ((1 : ℤ) : R) * X 3 2 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 14
  have d0_8_22 : X 8 6 * ((3 : ℤ) : R) + X 8 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 23 22 + ((0 : ℤ) : R) * X 0 22) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 8 22
  have d1_11_22 : X 11 9 * ((3 : ℤ) : R) + X 11 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 23 22 + ((0 : ℤ) : R) * X 0 22) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 11 22
  have d2_0_6 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 8 6 + ((0 : ℤ) : R) * X 0 6) =
      ((-3 : ℤ) : R) * X 3 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 0 6
  have d0_11_24 : X 11 10 * ((3 : ℤ) : R) + X 11 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 11 24
  have c12 : ((1 : ℤ) : R) * X 0 0 + ((1 : ℤ) : R) * X 11 11 = 0 := hc 12
  have i13 : X 0 0 = 0 := hi 13
  have d0_11_25 : X 11 12 * ((-1 : ℤ) : R) + X 11 13 * ((2 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 11 25
  have d2_1_13 : X 1 0 * ((0 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 11 13 + ((0 : ℤ) : R) * X 0 13) =
      ((-3 : ℤ) : R) * X 1 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 1 13
  have i11 : X 1 2 = 0 := hi 11
  have d2_1_14 : X 1 0 * ((0 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 11 14 + ((0 : ℤ) : R) * X 0 14) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 1 14
  have d0_8_25 : X 8 12 * ((-1 : ℤ) : R) + X 8 13 * ((2 : ℤ) : R) -
        (((3 : ℤ) : R) * X 23 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 8 25
  have d1_11_25 : X 11 15 * ((3 : ℤ) : R) + X 11 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 23 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 11 25
  have d2_0_12 : X 0 2 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 8 12 + ((0 : ℤ) : R) * X 0 12) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 0 12
  have i8 : X 0 2 = 0 := hi 8
  have c9 : ((1 : ℤ) : R) * X 1 5 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 9
  have d2_1_16 : X 1 5 * ((-3 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 11 16 + ((0 : ℤ) : R) * X 0 16) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 1 16
  have d2_1_17 : X 1 0 * ((0 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 11 17 + ((0 : ℤ) : R) * X 0 17) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 1 17
  have c6 : ((1 : ℤ) : R) * X 1 6 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 6
  have d2_1_18 : X 1 6 * ((-3 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 11 18 + ((0 : ℤ) : R) * X 0 18) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 1 18
  have d0_4_25 : X 4 12 * ((-1 : ℤ) : R) + X 4 13 * ((2 : ℤ) : R) -
        (((3 : ℤ) : R) * X 20 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 4 25
  have d2_1_19 : X 1 7 * ((-3 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 11 19 + ((0 : ℤ) : R) * X 0 19) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 1 19
  have d2_9_25 : X 9 17 * ((3 : ℤ) : R) + X 9 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 20 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 9 25
  have d3_1_17 : X 1 7 * ((3 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 9 17 + ((0 : ℤ) : R) * X 0 17) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 1 17
  have d5_0_12 : X 0 5 * ((-3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 4 12 + ((0 : ℤ) : R) * X 0 12) =
      ((0 : ℤ) : R) * X 0 5 + ((0 : ℤ) : R) * X 0 5 :=
    hX.entry 5 0 12
  have i4 : X 0 5 = 0 := hi 4
  have d0_3_25 : X 3 12 * ((-1 : ℤ) : R) + X 3 13 * ((2 : ℤ) : R) -
        (((3 : ℤ) : R) * X 19 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 3 25
  have d2_1_20 : X 1 9 * ((-3 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 11 20 + ((0 : ℤ) : R) * X 0 20) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 1 20
  have d2_7_25 : X 7 17 * ((3 : ℤ) : R) + X 7 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 19 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 7 25
  have d4_1_17 : X 1 9 * ((3 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 7 17 + ((0 : ℤ) : R) * X 0 17) =
      ((0 : ℤ) : R) * X 0 4 + ((0 : ℤ) : R) * X 0 4 :=
    hX.entry 4 1 17
  have d6_0_12 : X 0 6 * ((-3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 3 12 + ((0 : ℤ) : R) * X 0 12) =
      ((0 : ℤ) : R) * X 0 6 + ((0 : ℤ) : R) * X 0 6 :=
    hX.entry 6 0 12
  have i3 : X 0 6 = 0 := hi 3
  have d2_1_21 : X 1 0 * ((0 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 11 21 + ((0 : ℤ) : R) * X 0 21) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 1 21
  have d2_1_22 : X 1 0 * ((0 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 11 22 + ((0 : ℤ) : R) * X 0 22) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 1 22
  have d2_1_23 : X 1 12 * ((2 : ℤ) : R) + X 1 13 * ((-1 : ℤ) : R) -
        (((3 : ℤ) : R) * X 11 23 + ((0 : ℤ) : R) * X 0 23) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 1 23
  have d2_2_24 : X 2 14 * ((3 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 12 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 2 24
  have d3_1_22 : X 1 12 * ((-2 : ℤ) : R) + X 1 13 * ((1 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 9 22 + ((0 : ℤ) : R) * X 0 22) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 1 22
  have d4_4_24 : X 4 18 * ((3 : ℤ) : R) + X 4 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 12 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 4 + ((0 : ℤ) : R) * X 0 4 :=
    hX.entry 4 4 24
  have d5_0_18 : X 0 10 * ((-3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 4 18 + ((0 : ℤ) : R) * X 0 18) =
      ((0 : ℤ) : R) * X 0 5 + ((0 : ℤ) : R) * X 0 5 :=
    hX.entry 5 0 18
  have d5_2_22 : X 2 14 * ((-3 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 9 22 + ((0 : ℤ) : R) * X 0 22) =
      ((0 : ℤ) : R) * X 0 5 + ((0 : ℤ) : R) * X 0 5 :=
    hX.entry 5 2 22
  have i1 : X 0 10 = 0 := hi 1
  have d5_3_24 : X 3 0 * ((0 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 11 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 5 + ((0 : ℤ) : R) * X 0 5 :=
    hX.entry 5 3 24
  have c2 : ((1 : ℤ) : R) * X 0 14 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 2
  have d5_3_25 : X 3 21 * ((3 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 11 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 5 + ((0 : ℤ) : R) * X 0 5 :=
    hX.entry 5 3 25
  have d6_0_21 : X 0 14 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 3 21 + ((0 : ℤ) : R) * X 0 21) =
      ((0 : ℤ) : R) * X 0 6 + ((0 : ℤ) : R) * X 0 6 :=
    hX.entry 6 0 21
  fin_cases n
  · exact (show X 11 0 = 0 by linear_combination c22)
  · exact (show X 11 1 = 0 by
      linear_combination d0_11_15 + i23 + ((-2 : R) * X 8 0) * htwo +
        ((-1 : R) * X 11 1) * htwo)
  · exact (show X 11 2 = 0 by linear_combination d0_11_17 + ((-1 : R) * X 11 2) * htwo)
  · exact (show X 11 3 = 0 by
      linear_combination d0_11_19 + i20 + ((1 : R) * X 4 0) * htwo + ((-1 : R) * X 11 3) * htwo)
  · exact (show X 11 4 = 0 by
      linear_combination d0_11_20 + i19 + ((-2 : R) * X 3 0) * htwo +
        ((-1 : R) * X 11 4) * htwo)
  · exact (show X 11 5 = 0 by linear_combination d0_11_21 + ((-1 : R) * X 11 5) * htwo)
  · exact (show X 11 6 = 0 by linear_combination d0_11_22 + ((-1 : R) * X 11 6) * htwo)
  · exact (show X 11 7 = 0 by
      linear_combination c17 + d0_8_21 + d1_11_21 + d2_0_5 + ((1 : R) * X 4 2) * htwo +
        ((-1 : R) * X 11 7) * htwo + ((3 : R) * X 23 21) * htwo)
  · exact (show X 11 8 = 0 by
      linear_combination d0_11_23 + i15 + ((1 : R) * X 1 0) * htwo + ((-1 : R) * X 11 8) * htwo)
  · exact (show X 11 9 = 0 by
      linear_combination c14 + d0_8_22 + d1_11_22 + d2_0_6 + ((-2 : R) * X 3 2) * htwo +
        ((-1 : R) * X 11 9) * htwo + ((3 : R) * X 23 22) * htwo)
  · exact (show X 11 10 = 0 by linear_combination d0_11_24 + ((-1 : R) * X 11 10) * htwo)
  · exact (show X 11 11 = 0 by linear_combination c12 + i13 + ((-1 : R) * X 0 0) * htwo)
  · exact (show X 11 12 = 0 by
      linear_combination d0_11_25 + ((1 : R) * X 11 12) * htwo + ((-1 : R) * X 11 13) * htwo)
  · exact (show X 11 13 = 0 by
      linear_combination d2_1_13 + i11 + ((-2 : R) * X 1 2) * htwo + ((2 : R) * X 11 13) * htwo)
  · exact (show X 11 14 = 0 by linear_combination d2_1_14 + ((2 : R) * X 11 14) * htwo)
  · exact (show X 11 15 = 0 by
      linear_combination d0_8_25 + d1_11_25 + d2_0_12 + i8 + ((-2 : R) * X 0 2) * htwo +
        ((2 : R) * X 8 12) * htwo + ((-1 : R) * X 8 13) * htwo + ((-1 : R) * X 11 15) * htwo +
        ((3 : R) * X 23 25) * htwo)
  · exact (show X 11 16 = 0 by
      linear_combination c9 + d2_1_16 + ((1 : R) * X 1 5) * htwo + ((2 : R) * X 11 16) * htwo)
  · exact (show X 11 17 = 0 by linear_combination d2_1_17 + ((2 : R) * X 11 17) * htwo)
  · exact (show X 11 18 = 0 by
      linear_combination c6 + d2_1_18 + ((1 : R) * X 1 6) * htwo + ((2 : R) * X 11 18) * htwo)
  · exact (show X 11 19 = 0 by
      linear_combination d0_4_25 + d2_1_19 + d2_9_25 + d3_1_17 + d5_0_12 + i4 +
        ((1 : R) * X 0 5) * htwo + ((2 : R) * X 4 12) * htwo + ((-1 : R) * X 4 13) * htwo +
        ((-3 : R) * X 9 17) * htwo + ((2 : R) * X 11 19) * htwo)
  · exact (show X 11 20 = 0 by
      linear_combination d0_3_25 + d2_1_20 + d2_7_25 + d4_1_17 + d6_0_12 + i3 +
        ((1 : R) * X 0 6) * htwo + ((-1 : R) * X 3 12) * htwo + ((-1 : R) * X 3 13) * htwo +
        ((2 : R) * X 11 20) * htwo)
  · exact (show X 11 21 = 0 by linear_combination d2_1_21 + ((2 : R) * X 11 21) * htwo)
  · exact (show X 11 22 = 0 by linear_combination d2_1_22 + ((2 : R) * X 11 22) * htwo)
  · exact (show X 11 23 = 0 by
      linear_combination d2_1_23 + d2_2_24 + d3_1_22 + d4_4_24 + d5_0_18 + d5_2_22 + i1 +
        ((1 : R) * X 0 10) * htwo + ((-3 : R) * X 9 22) * htwo + ((2 : R) * X 11 23) * htwo +
        ((3 : R) * X 12 24) * htwo)
  · exact (show X 11 24 = 0 by linear_combination d5_3_24 + ((-1 : R) * X 11 24) * htwo)
  · exact (show X 11 25 = 0 by
      linear_combination c2 + d5_3_25 + d6_0_21 + ((-2 : R) * X 0 14) * htwo +
        ((-3 : R) * X 3 21) * htwo + ((-1 : R) * X 11 25) * htwo)

/-- Every entry of the `12`th row of a derivation all of whose coordinates vanish
is zero. -/
theorem entry_row_12 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hq : ∀ p, quotientCoordinate p X = 0) (hi : ∀ a, X (idealRow a) (idealCol a) = 0)
    (n : Fin 26) : X 12 n = 0 := by
  have htwo : (2 : R) = 0 := by exact_mod_cast CharP.cast_eq_zero R 2
  have hc := quotientCoordinate_entries hq
  have i25 : X 12 0 = 0 := hi 25
  have d0_14_17 : X 14 2 * ((3 : ℤ) : R) + X 14 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 17 + ((0 : ℤ) : R) * X 0 17) =
      ((-3 : ℤ) : R) * X 10 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 14 17
  have d1_2_2 : X 2 0 * ((0 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 14 2 + ((0 : ℤ) : R) * X 0 2) =
      ((3 : ℤ) : R) * X 12 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 2 2
  have i24 : X 10 0 = 0 := hi 24
  have d2_3_3 : X 3 0 * ((0 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3) =
      ((3 : ℤ) : R) * X 12 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 3 3
  have d2_2_3 : X 2 0 * ((0 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 12 3 + ((0 : ℤ) : R) * X 0 3) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 2 3
  have d2_2_4 : X 2 0 * ((0 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 12 4 + ((0 : ℤ) : R) * X 0 4) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 2 4
  have d0_0_5 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 13 5 + ((0 : ℤ) : R) * X 0 5) =
      ((3 : ℤ) : R) * X 4 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 0 5
  have d1_1_5 : X 1 0 * ((0 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 12 5 + ((-3 : ℤ) : R) * X 13 5) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 1 5
  have i20 : X 4 0 = 0 := hi 20
  have d0_0_6 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 13 6 + ((0 : ℤ) : R) * X 0 6) =
      ((-3 : ℤ) : R) * X 3 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 0 6
  have d1_1_6 : X 1 0 * ((0 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 12 6 + ((-3 : ℤ) : R) * X 13 6) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 1 6
  have i19 : X 3 0 = 0 := hi 19
  have d0_10_21 : X 10 5 * ((3 : ℤ) : R) + X 10 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 24 21 + ((0 : ℤ) : R) * X 0 21) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 10 21
  have d1_0_5 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 10 5 + ((0 : ℤ) : R) * X 0 5) =
      ((3 : ℤ) : R) * X 4 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 0 5
  have d1_12_21 : X 12 7 * ((3 : ℤ) : R) + X 12 0 * ((0 : ℤ) : R) -
        (((1 : ℤ) : R) * X 24 21 + ((0 : ℤ) : R) * X 0 21) =
      ((2 : ℤ) : R) * X 4 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 12 21
  have i18 : X 4 1 = 0 := hi 18
  have d0_0_8 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 13 8 + ((0 : ℤ) : R) * X 0 8) =
      ((3 : ℤ) : R) * X 2 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 0 8
  have d1_1_8 : X 1 0 * ((0 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 12 8 + ((-3 : ℤ) : R) * X 13 8) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 1 8
  have i17 : X 2 0 = 0 := hi 17
  have d0_10_22 : X 10 6 * ((3 : ℤ) : R) + X 10 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 24 22 + ((0 : ℤ) : R) * X 0 22) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 10 22
  have d1_0_6 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 10 6 + ((0 : ℤ) : R) * X 0 6) =
      ((-3 : ℤ) : R) * X 3 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 0 6
  have d1_12_22 : X 12 9 * ((3 : ℤ) : R) + X 12 0 * ((0 : ℤ) : R) -
        (((1 : ℤ) : R) * X 24 22 + ((0 : ℤ) : R) * X 0 22) =
      ((-2 : ℤ) : R) * X 3 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 12 22
  have i16 : X 3 1 = 0 := hi 16
  have d2_2_10 : X 2 0 * ((0 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 12 10 + ((0 : ℤ) : R) * X 0 10) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 2 10
  have d0_10_23 : X 10 8 * ((3 : ℤ) : R) + X 10 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 24 23 + ((0 : ℤ) : R) * X 0 23) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 10 23
  have d1_0_8 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 10 8 + ((0 : ℤ) : R) * X 0 8) =
      ((3 : ℤ) : R) * X 2 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 0 8
  have d1_12_23 : X 12 11 * ((3 : ℤ) : R) + X 12 0 * ((0 : ℤ) : R) -
        (((1 : ℤ) : R) * X 24 23 + ((0 : ℤ) : R) * X 0 23) =
      ((2 : ℤ) : R) * X 2 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 12 23
  have i14 : X 2 1 = 0 := hi 14
  have d2_2_12 : X 2 2 * ((3 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 12 12 + ((0 : ℤ) : R) * X 0 12) =
      ((3 : ℤ) : R) * X 2 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 2 12
  have d2_2_13 : X 2 0 * ((0 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 12 13 + ((0 : ℤ) : R) * X 0 13) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 2 13
  have d2_2_14 : X 2 0 * ((0 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 12 14 + ((0 : ℤ) : R) * X 0 14) =
      ((-3 : ℤ) : R) * X 1 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 2 14
  have i11 : X 1 2 = 0 := hi 11
  have d2_2_15 : X 2 0 * ((0 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 12 15 + ((0 : ℤ) : R) * X 0 15) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 2 15
  have d2_2_16 : X 2 5 * ((-3 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 12 16 + ((0 : ℤ) : R) * X 0 16) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 2 16
  have d3_2_14 : X 2 5 * ((3 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 14 + ((0 : ℤ) : R) * X 0 14) =
      ((-3 : ℤ) : R) * X 1 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 2 14
  have i9 : X 1 3 = 0 := hi 9
  have d0_0_17 : X 0 2 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 13 17 + ((0 : ℤ) : R) * X 0 17) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 0 17
  have d1_1_17 : X 1 0 * ((0 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 12 17 + ((-3 : ℤ) : R) * X 13 17) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 1 17
  have i8 : X 0 2 = 0 := hi 8
  have d0_3_23 : X 3 8 * ((3 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 19 23 + ((0 : ℤ) : R) * X 0 23) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 3 23
  have d2_7_23 : X 7 12 * ((2 : ℤ) : R) + X 7 13 * ((-1 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 19 23 + ((0 : ℤ) : R) * X 0 23) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 7 23
  have d3_3_18 : X 3 8 * ((-3 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 12 18 + ((0 : ℤ) : R) * X 0 18) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 3 18
  have d4_1_13 : X 1 0 * ((0 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 7 13 + ((0 : ℤ) : R) * X 0 13) =
      ((-3 : ℤ) : R) * X 1 4 + ((0 : ℤ) : R) * X 0 4 :=
    hX.entry 4 1 13
  have i7 : X 1 4 = 0 := hi 7
  have d0_0_19 : X 0 3 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 13 19 + ((0 : ℤ) : R) * X 0 19) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 0 19
  have d1_1_19 : X 1 0 * ((0 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 12 19 + ((-3 : ℤ) : R) * X 13 19) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 1 19
  have i6 : X 0 3 = 0 := hi 6
  have d0_0_20 : X 0 4 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 13 20 + ((0 : ℤ) : R) * X 0 20) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 0 20
  have d1_1_20 : X 1 0 * ((0 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 12 20 + ((-3 : ℤ) : R) * X 13 20) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 1 20
  have i5 : X 0 4 = 0 := hi 5
  have d2_2_21 : X 2 0 * ((0 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 12 21 + ((0 : ℤ) : R) * X 0 21) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 2 21
  have d2_2_22 : X 2 0 * ((0 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 12 22 + ((0 : ℤ) : R) * X 0 22) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 2 22
  have d3_3_23 : X 3 0 * ((0 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 12 23 + ((0 : ℤ) : R) * X 0 23) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 3 23
  have d4_4_24 : X 4 18 * ((3 : ℤ) : R) + X 4 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 12 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 4 + ((0 : ℤ) : R) * X 0 4 :=
    hX.entry 4 4 24
  have d5_0_18 : X 0 10 * ((-3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 4 18 + ((0 : ℤ) : R) * X 0 18) =
      ((0 : ℤ) : R) * X 0 5 + ((0 : ℤ) : R) * X 0 5 :=
    hX.entry 5 0 18
  have i1 : X 0 10 = 0 := hi 1
  have d2_2_25 : X 2 17 * ((3 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 12 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 2 25
  have d3_0_22 : X 0 12 * ((-2 : ℤ) : R) + X 0 13 * ((1 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 6 22 + ((0 : ℤ) : R) * X 0 22) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 0 22
  have d7_2_22 : X 2 17 * ((-3 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 6 22 + ((0 : ℤ) : R) * X 0 22) =
      ((0 : ℤ) : R) * X 0 7 + ((0 : ℤ) : R) * X 0 7 :=
    hX.entry 7 2 22
  have i0 : X 0 13 = 0 := hi 0
  fin_cases n
  · exact (show X 12 0 = 0 by linear_combination i25)
  · exact (show X 12 1 = 0 by
      linear_combination d0_14_17 + d1_2_2 + i24 + ((-2 : R) * X 10 0) * htwo +
        ((2 : R) * X 12 1) * htwo + ((-3 : R) * X 14 2) * htwo)
  · exact (show X 12 2 = 0 by linear_combination d2_3_3 + ((2 : R) * X 12 2) * htwo)
  · exact (show X 12 3 = 0 by linear_combination d2_2_3 + ((2 : R) * X 12 3) * htwo)
  · exact (show X 12 4 = 0 by linear_combination d2_2_4 + ((2 : R) * X 12 4) * htwo)
  · exact (show X 12 5 = 0 by
      linear_combination d0_0_5 + d1_1_5 + i20 + ((1 : R) * X 4 0) * htwo +
        ((-1 : R) * X 12 5) * htwo)
  · exact (show X 12 6 = 0 by
      linear_combination d0_0_6 + d1_1_6 + i19 + ((-2 : R) * X 3 0) * htwo +
        ((-1 : R) * X 12 6) * htwo)
  · exact (show X 12 7 = 0 by
      linear_combination d0_10_21 + d1_0_5 + d1_12_21 + i18 + ((2 : R) * X 4 1) * htwo +
        ((-3 : R) * X 10 5) * htwo + ((-1 : R) * X 12 7) * htwo + ((2 : R) * X 24 21) * htwo)
  · exact (show X 12 8 = 0 by
      linear_combination d0_0_8 + d1_1_8 + i17 + ((1 : R) * X 2 0) * htwo +
        ((-1 : R) * X 12 8) * htwo)
  · exact (show X 12 9 = 0 by
      linear_combination d0_10_22 + d1_0_6 + d1_12_22 + i16 + ((-3 : R) * X 3 1) * htwo +
        ((-3 : R) * X 10 6) * htwo + ((-1 : R) * X 12 9) * htwo + ((2 : R) * X 24 22) * htwo)
  · exact (show X 12 10 = 0 by linear_combination d2_2_10 + ((2 : R) * X 12 10) * htwo)
  · exact (show X 12 11 = 0 by
      linear_combination d0_10_23 + d1_0_8 + d1_12_23 + i14 + ((2 : R) * X 2 1) * htwo +
        ((-3 : R) * X 10 8) * htwo + ((-1 : R) * X 12 11) * htwo + ((2 : R) * X 24 23) * htwo)
  · exact (show X 12 12 = 0 by linear_combination d2_2_12 + ((2 : R) * X 12 12) * htwo)
  · exact (show X 12 13 = 0 by linear_combination d2_2_13 + ((2 : R) * X 12 13) * htwo)
  · exact (show X 12 14 = 0 by
      linear_combination d2_2_14 + i11 + ((-2 : R) * X 1 2) * htwo + ((2 : R) * X 12 14) * htwo)
  · exact (show X 12 15 = 0 by linear_combination d2_2_15 + ((2 : R) * X 12 15) * htwo)
  · exact (show X 12 16 = 0 by
      linear_combination d2_2_16 + d3_2_14 + i9 + ((-2 : R) * X 1 3) * htwo +
        ((2 : R) * X 12 16) * htwo)
  · exact (show X 12 17 = 0 by
      linear_combination d0_0_17 + d1_1_17 + i8 + ((-2 : R) * X 0 2) * htwo +
        ((-1 : R) * X 12 17) * htwo)
  · exact (show X 12 18 = 0 by
      linear_combination d0_3_23 + d2_7_23 + d3_3_18 + d4_1_13 + i7 + ((-2 : R) * X 1 4) * htwo +
        ((-1 : R) * X 7 12) * htwo + ((2 : R) * X 7 13) * htwo + ((2 : R) * X 12 18) * htwo)
  · exact (show X 12 19 = 0 by
      linear_combination d0_0_19 + d1_1_19 + i6 + ((-2 : R) * X 0 3) * htwo +
        ((-1 : R) * X 12 19) * htwo)
  · exact (show X 12 20 = 0 by
      linear_combination d0_0_20 + d1_1_20 + i5 + ((-2 : R) * X 0 4) * htwo +
        ((-1 : R) * X 12 20) * htwo)
  · exact (show X 12 21 = 0 by linear_combination d2_2_21 + ((2 : R) * X 12 21) * htwo)
  · exact (show X 12 22 = 0 by linear_combination d2_2_22 + ((2 : R) * X 12 22) * htwo)
  · exact (show X 12 23 = 0 by linear_combination d3_3_23 + ((2 : R) * X 12 23) * htwo)
  · exact (show X 12 24 = 0 by
      linear_combination d4_4_24 + d5_0_18 + i1 + ((1 : R) * X 0 10) * htwo +
        ((2 : R) * X 12 24) * htwo)
  · exact (show X 12 25 = 0 by
      linear_combination d2_2_25 + d3_0_22 + d7_2_22 + i0 + ((1 : R) * X 0 12) * htwo +
        ((-1 : R) * X 0 13) * htwo + ((2 : R) * X 12 25) * htwo)

/-- Every entry of the `13`th row of a derivation all of whose coordinates vanish
is zero. -/
theorem entry_row_13 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hq : ∀ p, quotientCoordinate p X = 0) (hi : ∀ a, X (idealRow a) (idealCol a) = 0)
    (n : Fin 26) : X 13 n = 0 := by
  have htwo : (2 : R) = 0 := by exact_mod_cast CharP.cast_eq_zero R 2
  have hc := quotientCoordinate_entries hq
  have d0_7_7 : X 7 0 * ((0 : ℤ) : R) + X 7 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 7 + ((0 : ℤ) : R) * X 0 7) =
      ((3 : ℤ) : R) * X 13 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 7 7
  have d0_0_1 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 13 1 + ((0 : ℤ) : R) * X 0 1) =
      ((-3 : ℤ) : R) * X 10 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 0 1
  have i24 : X 10 0 = 0 := hi 24
  have d0_0_2 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 13 2 + ((0 : ℤ) : R) * X 0 2) =
      ((3 : ℤ) : R) * X 8 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 0 2
  have i23 : X 8 0 = 0 := hi 23
  have d0_0_3 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 13 3 + ((0 : ℤ) : R) * X 0 3) =
      ((-3 : ℤ) : R) * X 6 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 0 3
  have i22 : X 6 0 = 0 := hi 22
  have d0_0_4 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 13 4 + ((0 : ℤ) : R) * X 0 4) =
      ((3 : ℤ) : R) * X 5 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 0 4
  have i21 : X 5 0 = 0 := hi 21
  have d0_0_5 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 13 5 + ((0 : ℤ) : R) * X 0 5) =
      ((3 : ℤ) : R) * X 4 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 0 5
  have i20 : X 4 0 = 0 := hi 20
  have d0_0_6 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 13 6 + ((0 : ℤ) : R) * X 0 6) =
      ((-3 : ℤ) : R) * X 3 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 0 6
  have i19 : X 3 0 = 0 := hi 19
  have d0_0_7 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 13 7 + ((0 : ℤ) : R) * X 0 7) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 0 7
  have d0_0_8 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 13 8 + ((0 : ℤ) : R) * X 0 8) =
      ((3 : ℤ) : R) * X 2 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 0 8
  have i17 : X 2 0 = 0 := hi 17
  have d0_0_9 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 13 9 + ((0 : ℤ) : R) * X 0 9) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 0 9
  have d0_0_10 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 13 10 + ((0 : ℤ) : R) * X 0 10) =
      ((-3 : ℤ) : R) * X 1 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 0 10
  have i15 : X 1 0 = 0 := hi 15
  have d0_0_11 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 13 11 + ((0 : ℤ) : R) * X 0 11) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 0 11
  have d0_0_12 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 13 12 + ((0 : ℤ) : R) * X 0 12) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 0 12
  have d0_0_13 : X 0 0 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 13 13 + ((0 : ℤ) : R) * X 0 13) =
      ((3 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 0 13
  have d0_0_14 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 13 14 + ((0 : ℤ) : R) * X 0 14) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 0 14
  have d0_0_15 : X 0 1 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 13 15 + ((0 : ℤ) : R) * X 0 15) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 0 15
  have i10 : X 0 1 = 0 := hi 10
  have d0_0_16 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 13 16 + ((0 : ℤ) : R) * X 0 16) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 0 16
  have d0_0_17 : X 0 2 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 13 17 + ((0 : ℤ) : R) * X 0 17) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 0 17
  have i8 : X 0 2 = 0 := hi 8
  have d0_0_18 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 13 18 + ((0 : ℤ) : R) * X 0 18) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 0 18
  have d0_0_19 : X 0 3 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 13 19 + ((0 : ℤ) : R) * X 0 19) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 0 19
  have i6 : X 0 3 = 0 := hi 6
  have d0_0_20 : X 0 4 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 13 20 + ((0 : ℤ) : R) * X 0 20) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 0 20
  have i5 : X 0 4 = 0 := hi 5
  have d0_0_21 : X 0 5 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 13 21 + ((0 : ℤ) : R) * X 0 21) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 0 21
  have i4 : X 0 5 = 0 := hi 4
  have d0_0_22 : X 0 6 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 13 22 + ((0 : ℤ) : R) * X 0 22) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 0 22
  have i3 : X 0 6 = 0 := hi 3
  have d0_0_23 : X 0 8 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 13 23 + ((0 : ℤ) : R) * X 0 23) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 0 23
  have i2 : X 0 8 = 0 := hi 2
  have d0_0_24 : X 0 10 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 13 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 0 24
  have i1 : X 0 10 = 0 := hi 1
  have d7_7_25 : X 7 0 * ((0 : ℤ) : R) + X 7 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 13 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 7 + ((0 : ℤ) : R) * X 0 7 :=
    hX.entry 7 7 25
  fin_cases n
  · exact (show X 13 0 = 0 by linear_combination d0_7_7 + ((2 : R) * X 13 0) * htwo)
  · exact (show X 13 1 = 0 by
      linear_combination d0_0_1 + i24 + ((-2 : R) * X 10 0) * htwo + ((2 : R) * X 13 1) * htwo)
  · exact (show X 13 2 = 0 by
      linear_combination d0_0_2 + i23 + ((1 : R) * X 8 0) * htwo + ((2 : R) * X 13 2) * htwo)
  · exact (show X 13 3 = 0 by
      linear_combination d0_0_3 + i22 + ((-2 : R) * X 6 0) * htwo + ((2 : R) * X 13 3) * htwo)
  · exact (show X 13 4 = 0 by
      linear_combination d0_0_4 + i21 + ((1 : R) * X 5 0) * htwo + ((2 : R) * X 13 4) * htwo)
  · exact (show X 13 5 = 0 by
      linear_combination d0_0_5 + i20 + ((1 : R) * X 4 0) * htwo + ((2 : R) * X 13 5) * htwo)
  · exact (show X 13 6 = 0 by
      linear_combination d0_0_6 + i19 + ((-2 : R) * X 3 0) * htwo + ((2 : R) * X 13 6) * htwo)
  · exact (show X 13 7 = 0 by linear_combination d0_0_7 + ((2 : R) * X 13 7) * htwo)
  · exact (show X 13 8 = 0 by
      linear_combination d0_0_8 + i17 + ((1 : R) * X 2 0) * htwo + ((2 : R) * X 13 8) * htwo)
  · exact (show X 13 9 = 0 by linear_combination d0_0_9 + ((2 : R) * X 13 9) * htwo)
  · exact (show X 13 10 = 0 by
      linear_combination d0_0_10 + i15 + ((-2 : R) * X 1 0) * htwo + ((2 : R) * X 13 10) * htwo)
  · exact (show X 13 11 = 0 by linear_combination d0_0_11 + ((2 : R) * X 13 11) * htwo)
  · exact (show X 13 12 = 0 by linear_combination d0_0_12 + ((2 : R) * X 13 12) * htwo)
  · exact (show X 13 13 = 0 by linear_combination d0_0_13 + ((2 : R) * X 13 13) * htwo)
  · exact (show X 13 14 = 0 by linear_combination d0_0_14 + ((2 : R) * X 13 14) * htwo)
  · exact (show X 13 15 = 0 by
      linear_combination d0_0_15 + i10 + ((-2 : R) * X 0 1) * htwo + ((2 : R) * X 13 15) * htwo)
  · exact (show X 13 16 = 0 by linear_combination d0_0_16 + ((2 : R) * X 13 16) * htwo)
  · exact (show X 13 17 = 0 by
      linear_combination d0_0_17 + i8 + ((-2 : R) * X 0 2) * htwo + ((2 : R) * X 13 17) * htwo)
  · exact (show X 13 18 = 0 by linear_combination d0_0_18 + ((2 : R) * X 13 18) * htwo)
  · exact (show X 13 19 = 0 by
      linear_combination d0_0_19 + i6 + ((-2 : R) * X 0 3) * htwo + ((2 : R) * X 13 19) * htwo)
  · exact (show X 13 20 = 0 by
      linear_combination d0_0_20 + i5 + ((-2 : R) * X 0 4) * htwo + ((2 : R) * X 13 20) * htwo)
  · exact (show X 13 21 = 0 by
      linear_combination d0_0_21 + i4 + ((-2 : R) * X 0 5) * htwo + ((2 : R) * X 13 21) * htwo)
  · exact (show X 13 22 = 0 by
      linear_combination d0_0_22 + i3 + ((-2 : R) * X 0 6) * htwo + ((2 : R) * X 13 22) * htwo)
  · exact (show X 13 23 = 0 by
      linear_combination d0_0_23 + i2 + ((-2 : R) * X 0 8) * htwo + ((2 : R) * X 13 23) * htwo)
  · exact (show X 13 24 = 0 by
      linear_combination d0_0_24 + i1 + ((-2 : R) * X 0 10) * htwo + ((2 : R) * X 13 24) * htwo)
  · exact (show X 13 25 = 0 by linear_combination d7_7_25 + ((2 : R) * X 13 25) * htwo)

end TauCeti.F4ShortRoot
