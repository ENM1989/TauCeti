/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.IdealCoordinate

/-!
# Rows 4 to 6 of a derivation with vanishing coordinates

A matrix differentiating the invariant symmetric multiplication of the twenty-six-dimensional
module of type `F₄` modulo two, and annihilated by the twenty-six short-root quotient coordinates
and by the twenty-six ideal coordinates, is zero. This file proves that for the entries in rows
4 to 6.

The derivation equations are graded by the weight of the entry they constrain, so each entry is
determined by the few equations of its own weight together with the vanishing coordinates of that
weight; the proof of each entry is that combination. The equations themselves are the entrywise
form `TauCeti.F4ShortRoot.IsDerivation.entry` of the derivation equations, instantiated at the
relevant indices, and each combination is exact up to multiples of two, which vanish in
characteristic two.

## Main results

* `TauCeti.F4ShortRoot.entry_row_4` and its companions up to
  `TauCeti.F4ShortRoot.entry_row_6`: the entries of these rows vanish.
-/

public section

open Matrix

namespace TauCeti.F4ShortRoot

universe u

variable {R : Type u} [CommRing R] [CharP R 2]

/-- Every entry of the `4`th row of a derivation all of whose coordinates vanish
is zero. -/
theorem entry_row_4 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hq : ∀ p, quotientCoordinate p X = 0) (hi : ∀ a, X (idealRow a) (idealCol a) = 0)
    (n : Fin 26) : X 4 n = 0 := by
  have htwo : (2 : R) = 0 := by exact_mod_cast CharP.cast_eq_zero R 2
  have hc := quotientCoordinate_entries hq
  have i20 : X 4 0 = 0 := hi 20
  have i18 : X 4 1 = 0 := hi 18
  have c17 : ((1 : ℤ) : R) * X 4 2 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 17
  have c15 : ((1 : ℤ) : R) * X 4 3 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 15
  have c13 : ((1 : ℤ) : R) * X 0 0 + ((1 : ℤ) : R) * X 7 7 = 0 := hc 13
  have d0_5_21 : X 5 5 * ((3 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 21 21 + ((0 : ℤ) : R) * X 0 21) =
      ((3 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 5 21
  have d1_0_10 : X 0 0 * ((-3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 10 10 + ((0 : ℤ) : R) * X 0 10) =
      ((-3 : ℤ) : R) * X 1 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 0 10
  have d1_3_16 : X 3 3 * ((-3 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 16 16 + ((0 : ℤ) : R) * X 0 16) =
      ((-3 : ℤ) : R) * X 1 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 3 16
  have d1_4_18 : X 4 4 * ((-3 : ℤ) : R) + X 4 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 18 18 + ((0 : ℤ) : R) * X 0 18) =
      ((-3 : ℤ) : R) * X 1 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 4 18
  have d1_7_21 : X 7 7 * ((3 : ℤ) : R) + X 7 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 21 21 + ((0 : ℤ) : R) * X 0 21) =
      ((3 : ℤ) : R) * X 1 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 7 21
  have d2_5_16 : X 5 5 * ((-3 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 16 16 + ((0 : ℤ) : R) * X 0 16) =
      ((-3 : ℤ) : R) * X 2 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 5 16
  have d2_6_18 : X 6 6 * ((-3 : ℤ) : R) + X 6 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 18 18 + ((0 : ℤ) : R) * X 0 18) =
      ((-3 : ℤ) : R) * X 2 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 6 18
  have d3_0_6 : X 0 0 * ((-3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 6 6 + ((0 : ℤ) : R) * X 0 6) =
      ((-3 : ℤ) : R) * X 3 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 0 6
  have i12 : X 10 10 = 0 := hi 12
  have d2_4_16 : X 4 5 * ((-3 : ℤ) : R) + X 4 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 16 + ((0 : ℤ) : R) * X 0 16) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 4 16
  have d2_4_18 : X 4 6 * ((-3 : ℤ) : R) + X 4 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 18 + ((0 : ℤ) : R) * X 0 18) =
      ((-3 : ℤ) : R) * X 1 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 4 18
  have i11 : X 1 2 = 0 := hi 11
  have d2_4_19 : X 4 7 * ((-3 : ℤ) : R) + X 4 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 19 + ((0 : ℤ) : R) * X 0 19) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 4 19
  have d0_4_23 : X 4 8 * ((3 : ℤ) : R) + X 4 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 20 23 + ((0 : ℤ) : R) * X 0 23) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 4 23
  have d2_9_23 : X 9 12 * ((2 : ℤ) : R) + X 9 13 * ((-1 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 20 23 + ((0 : ℤ) : R) * X 0 23) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 9 23
  have d3_1_13 : X 1 0 * ((0 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 9 13 + ((0 : ℤ) : R) * X 0 13) =
      ((-3 : ℤ) : R) * X 1 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 1 13
  have i9 : X 1 3 = 0 := hi 9
  have d2_4_20 : X 4 9 * ((-3 : ℤ) : R) + X 4 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 20 + ((0 : ℤ) : R) * X 0 20) =
      ((3 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 4 20
  have i8 : X 0 2 = 0 := hi 8
  have c9 : ((1 : ℤ) : R) * X 1 5 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 9
  have d0_4_24 : X 4 10 * ((3 : ℤ) : R) + X 4 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 20 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 4 24
  have d2_9_24 : X 9 14 * ((3 : ℤ) : R) + X 9 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 20 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 9 24
  have d3_1_14 : X 1 5 * ((3 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 9 14 + ((0 : ℤ) : R) * X 0 14) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 1 14
  have d1_4_23 : X 4 11 * ((3 : ℤ) : R) + X 4 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 18 23 + ((0 : ℤ) : R) * X 0 23) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 4 23
  have d1_6_24 : X 6 12 * ((1 : ℤ) : R) + X 6 13 * ((1 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 6 24
  have d2_6_23 : X 6 12 * ((2 : ℤ) : R) + X 6 13 * ((-1 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 18 23 + ((0 : ℤ) : R) * X 0 23) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 6 23
  have d3_0_12 : X 0 3 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 6 12 + ((0 : ℤ) : R) * X 0 12) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 0 12
  have i6 : X 0 3 = 0 := hi 6
  have d5_0_12 : X 0 5 * ((-3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 4 12 + ((0 : ℤ) : R) * X 0 12) =
      ((0 : ℤ) : R) * X 0 5 + ((0 : ℤ) : R) * X 0 5 :=
    hX.entry 5 0 12
  have i4 : X 0 5 = 0 := hi 4
  have d2_4_23 : X 4 12 * ((2 : ℤ) : R) + X 4 13 * ((-1 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 23 + ((0 : ℤ) : R) * X 0 23) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 4 23
  have d2_4_24 : X 4 14 * ((3 : ℤ) : R) + X 4 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 4 24
  have c7 : ((1 : ℤ) : R) * X 0 7 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 7
  have d1_4_25 : X 4 15 * ((3 : ℤ) : R) + X 4 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 18 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 4 25
  have d2_6_25 : X 6 17 * ((3 : ℤ) : R) + X 6 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 18 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 6 25
  have d3_0_17 : X 0 7 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 6 17 + ((0 : ℤ) : R) * X 0 17) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 0 17
  have d3_4_24 : X 4 16 * ((3 : ℤ) : R) + X 4 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 4 24
  have d2_4_25 : X 4 17 * ((3 : ℤ) : R) + X 4 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 4 25
  have d5_0_18 : X 0 10 * ((-3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 4 18 + ((0 : ℤ) : R) * X 0 18) =
      ((0 : ℤ) : R) * X 0 5 + ((0 : ℤ) : R) * X 0 5 :=
    hX.entry 5 0 18
  have i1 : X 0 10 = 0 := hi 1
  have d3_4_25 : X 4 19 * ((3 : ℤ) : R) + X 4 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 4 25
  have d2_2_25 : X 2 17 * ((3 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 12 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 2 25
  have d3_0_22 : X 0 12 * ((-2 : ℤ) : R) + X 0 13 * ((1 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 6 22 + ((0 : ℤ) : R) * X 0 22) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 0 22
  have d4_4_25 : X 4 20 * ((3 : ℤ) : R) + X 4 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 12 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 4 + ((0 : ℤ) : R) * X 0 4 :=
    hX.entry 4 4 25
  have d7_2_22 : X 2 17 * ((-3 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 6 22 + ((0 : ℤ) : R) * X 0 22) =
      ((0 : ℤ) : R) * X 0 7 + ((0 : ℤ) : R) * X 0 7 :=
    hX.entry 7 2 22
  have i0 : X 0 13 = 0 := hi 0
  have d5_0_21 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 4 21 + ((0 : ℤ) : R) * X 0 21) =
      ((0 : ℤ) : R) * X 0 5 + ((0 : ℤ) : R) * X 0 5 :=
    hX.entry 5 0 21
  have c2 : ((1 : ℤ) : R) * X 0 14 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 2
  have d5_0_22 : X 0 14 * ((-3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 4 22 + ((0 : ℤ) : R) * X 0 22) =
      ((0 : ℤ) : R) * X 0 5 + ((0 : ℤ) : R) * X 0 5 :=
    hX.entry 5 0 22
  have c1 : ((1 : ℤ) : R) * X 0 16 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 1
  have d5_0_23 : X 0 16 * ((-3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 4 23 + ((0 : ℤ) : R) * X 0 23) =
      ((0 : ℤ) : R) * X 0 5 + ((0 : ℤ) : R) * X 0 5 :=
    hX.entry 5 0 23
  have d5_0_24 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 4 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 5 + ((0 : ℤ) : R) * X 0 5 :=
    hX.entry 5 0 24
  have d7_1_25 : X 1 0 * ((0 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 4 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 7 + ((0 : ℤ) : R) * X 0 7 :=
    hX.entry 7 1 25
  fin_cases n
  · exact (show X 4 0 = 0 by linear_combination i20)
  · exact (show X 4 1 = 0 by linear_combination i18)
  · exact (show X 4 2 = 0 by linear_combination c17)
  · exact (show X 4 3 = 0 by linear_combination c15)
  · exact (show X 4 4 = 0 by
      linear_combination c13 + d0_5_21 + d1_0_10 + d1_3_16 + d1_4_18 + d1_7_21 + d2_5_16 +
        d2_6_18 + d3_0_6 + i12 + ((4 : R) * X 0 0) * htwo + ((-3 : R) * X 1 1) * htwo +
        ((-3 : R) * X 2 2) * htwo + ((2 : R) * X 4 4) * htwo + ((-2 : R) * X 7 7) * htwo +
        ((-2 : R) * X 10 10) * htwo + ((-3 : R) * X 16 16) * htwo + ((-3 : R) * X 18 18) * htwo +
        ((3 : R) * X 21 21) * htwo)
  · exact (show X 4 5 = 0 by linear_combination d2_4_16 + ((2 : R) * X 4 5) * htwo)
  · exact (show X 4 6 = 0 by
      linear_combination d2_4_18 + i11 + ((-2 : R) * X 1 2) * htwo + ((2 : R) * X 4 6) * htwo)
  · exact (show X 4 7 = 0 by linear_combination d2_4_19 + ((2 : R) * X 4 7) * htwo)
  · exact (show X 4 8 = 0 by
      linear_combination d0_4_23 + d2_9_23 + d3_1_13 + i9 + ((-2 : R) * X 1 3) * htwo +
        ((-1 : R) * X 4 8) * htwo + ((-1 : R) * X 9 12) * htwo + ((-1 : R) * X 9 13) * htwo)
  · exact (show X 4 9 = 0 by
      linear_combination d2_4_20 + i8 + ((1 : R) * X 0 2) * htwo + ((2 : R) * X 4 9) * htwo)
  · exact (show X 4 10 = 0 by
      linear_combination c9 + d0_4_24 + d2_9_24 + d3_1_14 + ((-2 : R) * X 1 5) * htwo +
        ((-1 : R) * X 4 10) * htwo + ((-3 : R) * X 9 14) * htwo)
  · exact (show X 4 11 = 0 by
      linear_combination d1_4_23 + d1_6_24 + d2_6_23 + d3_0_12 + i6 + ((-2 : R) * X 0 3) * htwo +
        ((-1 : R) * X 4 11) * htwo + ((-3 : R) * X 6 12) * htwo + ((-3 : R) * X 18 23) * htwo)
  · exact (show X 4 12 = 0 by
      linear_combination d5_0_12 + i4 + ((1 : R) * X 0 5) * htwo + ((2 : R) * X 4 12) * htwo)
  · exact (show X 4 13 = 0 by
      linear_combination d2_4_23 + ((-1 : R) * X 4 12) * htwo + ((1 : R) * X 4 13) * htwo)
  · exact (show X 4 14 = 0 by linear_combination d2_4_24 + ((-1 : R) * X 4 14) * htwo)
  · exact (show X 4 15 = 0 by
      linear_combination c7 + d1_4_25 + d2_6_25 + d3_0_17 + ((-2 : R) * X 0 7) * htwo +
        ((-1 : R) * X 4 15) * htwo + ((-3 : R) * X 6 17) * htwo + ((-3 : R) * X 18 25) * htwo)
  · exact (show X 4 16 = 0 by linear_combination d3_4_24 + ((-1 : R) * X 4 16) * htwo)
  · exact (show X 4 17 = 0 by linear_combination d2_4_25 + ((-1 : R) * X 4 17) * htwo)
  · exact (show X 4 18 = 0 by
      linear_combination d5_0_18 + i1 + ((1 : R) * X 0 10) * htwo + ((2 : R) * X 4 18) * htwo)
  · exact (show X 4 19 = 0 by linear_combination d3_4_25 + ((-1 : R) * X 4 19) * htwo)
  · exact (show X 4 20 = 0 by
      linear_combination d2_2_25 + d3_0_22 + d4_4_25 + d7_2_22 + i0 + ((1 : R) * X 0 12) * htwo +
        ((-1 : R) * X 0 13) * htwo + ((-1 : R) * X 4 20) * htwo + ((3 : R) * X 12 25) * htwo)
  · exact (show X 4 21 = 0 by linear_combination d5_0_21 + ((2 : R) * X 4 21) * htwo)
  · exact (show X 4 22 = 0 by
      linear_combination c2 + d5_0_22 + ((1 : R) * X 0 14) * htwo + ((2 : R) * X 4 22) * htwo)
  · exact (show X 4 23 = 0 by
      linear_combination c1 + d5_0_23 + ((1 : R) * X 0 16) * htwo + ((2 : R) * X 4 23) * htwo)
  · exact (show X 4 24 = 0 by linear_combination d5_0_24 + ((2 : R) * X 4 24) * htwo)
  · exact (show X 4 25 = 0 by linear_combination d7_1_25 + ((2 : R) * X 4 25) * htwo)

/-- Every entry of the `5`th row of a derivation all of whose coordinates vanish
is zero. -/
theorem entry_row_5 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hq : ∀ p, quotientCoordinate p X = 0) (hi : ∀ a, X (idealRow a) (idealCol a) = 0)
    (n : Fin 26) : X 5 n = 0 := by
  have htwo : (2 : R) = 0 := by exact_mod_cast CharP.cast_eq_zero R 2
  have hc := quotientCoordinate_entries hq
  have i21 : X 5 0 = 0 := hi 21
  have c16 : ((1 : ℤ) : R) * X 5 1 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 16
  have d1_5_14 : X 5 2 * ((-3 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 14 + ((0 : ℤ) : R) * X 0 14) =
      ((3 : ℤ) : R) * X 3 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 5 14
  have i16 : X 3 1 = 0 := hi 16
  have d1_5_16 : X 5 3 * ((-3 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 16 + ((0 : ℤ) : R) * X 0 16) =
      ((-3 : ℤ) : R) * X 2 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 5 16
  have i14 : X 2 1 = 0 := hi 14
  have d1_5_18 : X 5 4 * ((-3 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 18 + ((0 : ℤ) : R) * X 0 18) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 5 18
  have c13 : ((1 : ℤ) : R) * X 0 0 + ((1 : ℤ) : R) * X 7 7 = 0 := hc 13
  have d0_5_21 : X 5 5 * ((3 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 21 21 + ((0 : ℤ) : R) * X 0 21) =
      ((3 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 5 21
  have d1_0_10 : X 0 0 * ((-3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 10 10 + ((0 : ℤ) : R) * X 0 10) =
      ((-3 : ℤ) : R) * X 1 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 0 10
  have d1_7_21 : X 7 7 * ((3 : ℤ) : R) + X 7 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 21 21 + ((0 : ℤ) : R) * X 0 21) =
      ((3 : ℤ) : R) * X 1 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 7 21
  have i12 : X 10 10 = 0 := hi 12
  have i13 : X 0 0 = 0 := hi 13
  have c10 : ((1 : ℤ) : R) * X 3 4 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 10
  have d1_3_18 : X 3 4 * ((-3 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 16 18 + ((0 : ℤ) : R) * X 0 18) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 3 18
  have d2_5_18 : X 5 6 * ((-3 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 16 18 + ((0 : ℤ) : R) * X 0 18) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 5 18
  have d1_5_21 : X 5 7 * ((3 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 21 + ((0 : ℤ) : R) * X 0 21) =
      ((3 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 5 21
  have i10 : X 0 1 = 0 := hi 10
  have c8 : ((1 : ℤ) : R) * X 2 4 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 8
  have d1_2_18 : X 2 4 * ((-3 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 14 18 + ((0 : ℤ) : R) * X 0 18) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 2 18
  have d3_5_18 : X 5 8 * ((-3 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 14 18 + ((0 : ℤ) : R) * X 0 18) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 5 18
  have d1_5_22 : X 5 9 * ((3 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 22 + ((0 : ℤ) : R) * X 0 22) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 5 22
  have d4_0_10 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 5 10 + ((0 : ℤ) : R) * X 0 10) =
      ((-3 : ℤ) : R) * X 1 4 + ((0 : ℤ) : R) * X 0 4 :=
    hX.entry 4 0 10
  have i7 : X 1 4 = 0 := hi 7
  have d1_5_23 : X 5 11 * ((3 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 23 + ((0 : ℤ) : R) * X 0 23) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 5 23
  have d0_0_20 : X 0 4 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 13 20 + ((0 : ℤ) : R) * X 0 20) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 0 20
  have d1_1_20 : X 1 0 * ((0 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 12 20 + ((-3 : ℤ) : R) * X 13 20) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 1 20
  have d1_3_23 : X 3 11 * ((3 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 16 23 + ((0 : ℤ) : R) * X 0 23) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 3 23
  have d1_5_24 : X 5 12 * ((1 : ℤ) : R) + X 5 13 * ((1 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 5 24
  have d2_5_23 : X 5 12 * ((2 : ℤ) : R) + X 5 13 * ((-1 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 16 23 + ((0 : ℤ) : R) * X 0 23) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 5 23
  have d3_3_20 : X 3 11 * ((-3 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 12 20 + ((0 : ℤ) : R) * X 0 20) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 3 20
  have i5 : X 0 4 = 0 := hi 5
  have d4_0_14 : X 0 6 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 5 14 + ((0 : ℤ) : R) * X 0 14) =
      ((0 : ℤ) : R) * X 0 4 + ((0 : ℤ) : R) * X 0 4 :=
    hX.entry 4 0 14
  have i3 : X 0 6 = 0 := hi 3
  have d1_5_25 : X 5 15 * ((3 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 5 25
  have d4_0_16 : X 0 8 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 5 16 + ((0 : ℤ) : R) * X 0 16) =
      ((0 : ℤ) : R) * X 0 4 + ((0 : ℤ) : R) * X 0 4 :=
    hX.entry 4 0 16
  have i2 : X 0 8 = 0 := hi 2
  have c5 : ((1 : ℤ) : R) * X 0 9 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 5
  have d4_0_17 : X 0 9 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 5 17 + ((0 : ℤ) : R) * X 0 17) =
      ((0 : ℤ) : R) * X 0 4 + ((0 : ℤ) : R) * X 0 4 :=
    hX.entry 4 0 17
  have d4_0_18 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 5 18 + ((0 : ℤ) : R) * X 0 18) =
      ((0 : ℤ) : R) * X 0 4 + ((0 : ℤ) : R) * X 0 4 :=
    hX.entry 4 0 18
  have c3 : ((1 : ℤ) : R) * X 0 11 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 3
  have d4_0_19 : X 0 11 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 5 19 + ((0 : ℤ) : R) * X 0 19) =
      ((0 : ℤ) : R) * X 0 4 + ((0 : ℤ) : R) * X 0 4 :=
    hX.entry 4 0 19
  have d4_0_20 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 5 20 + ((0 : ℤ) : R) * X 0 20) =
      ((0 : ℤ) : R) * X 0 4 + ((0 : ℤ) : R) * X 0 4 :=
    hX.entry 4 0 20
  have d4_0_21 : X 0 12 * ((2 : ℤ) : R) + X 0 13 * ((-1 : ℤ) : R) -
        (((3 : ℤ) : R) * X 5 21 + ((0 : ℤ) : R) * X 0 21) =
      ((0 : ℤ) : R) * X 0 4 + ((0 : ℤ) : R) * X 0 4 :=
    hX.entry 4 0 21
  have i0 : X 0 13 = 0 := hi 0
  have d4_0_22 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 5 22 + ((0 : ℤ) : R) * X 0 22) =
      ((0 : ℤ) : R) * X 0 4 + ((0 : ℤ) : R) * X 0 4 :=
    hX.entry 4 0 22
  have d4_0_23 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 5 23 + ((0 : ℤ) : R) * X 0 23) =
      ((0 : ℤ) : R) * X 0 4 + ((0 : ℤ) : R) * X 0 4 :=
    hX.entry 4 0 23
  have c0 : ((1 : ℤ) : R) * X 0 18 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 0
  have d4_0_24 : X 0 18 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 5 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 4 + ((0 : ℤ) : R) * X 0 4 :=
    hX.entry 4 0 24
  have d9_2_25 : X 2 0 * ((0 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 5 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 9 + ((0 : ℤ) : R) * X 0 9 :=
    hX.entry 9 2 25
  fin_cases n
  · exact (show X 5 0 = 0 by linear_combination i21)
  · exact (show X 5 1 = 0 by linear_combination c16)
  · exact (show X 5 2 = 0 by
      linear_combination d1_5_14 + i16 + ((1 : R) * X 3 1) * htwo + ((2 : R) * X 5 2) * htwo)
  · exact (show X 5 3 = 0 by
      linear_combination d1_5_16 + i14 + ((-2 : R) * X 2 1) * htwo + ((2 : R) * X 5 3) * htwo)
  · exact (show X 5 4 = 0 by linear_combination d1_5_18 + ((2 : R) * X 5 4) * htwo)
  · exact (show X 5 5 = 0 by
      linear_combination c13 + d0_5_21 + d1_0_10 + d1_7_21 + i12 + i13 +
        ((2 : R) * X 0 0) * htwo + ((-1 : R) * X 5 5) * htwo + ((-2 : R) * X 7 7) * htwo +
        ((-2 : R) * X 10 10) * htwo + ((3 : R) * X 21 21) * htwo)
  · exact (show X 5 6 = 0 by
      linear_combination c10 + d1_3_18 + d2_5_18 + ((1 : R) * X 3 4) * htwo +
        ((2 : R) * X 5 6) * htwo + ((-3 : R) * X 16 18) * htwo)
  · exact (show X 5 7 = 0 by
      linear_combination d1_5_21 + i10 + ((1 : R) * X 0 1) * htwo + ((-1 : R) * X 5 7) * htwo)
  · exact (show X 5 8 = 0 by
      linear_combination c8 + d1_2_18 + d3_5_18 + ((1 : R) * X 2 4) * htwo +
        ((2 : R) * X 5 8) * htwo)
  · exact (show X 5 9 = 0 by linear_combination d1_5_22 + ((-1 : R) * X 5 9) * htwo)
  · exact (show X 5 10 = 0 by
      linear_combination d4_0_10 + i7 + ((-2 : R) * X 1 4) * htwo + ((2 : R) * X 5 10) * htwo)
  · exact (show X 5 11 = 0 by linear_combination d1_5_23 + ((-1 : R) * X 5 11) * htwo)
  · exact (show X 5 12 = 0 by
      linear_combination d0_0_20 + d1_1_20 + d1_3_23 + d1_5_24 + d2_5_23 + d3_3_20 + i5 +
        ((-2 : R) * X 0 4) * htwo + ((-1 : R) * X 5 12) * htwo + ((-3 : R) * X 16 23) * htwo)
  · exact (show X 5 13 = 0 by
      linear_combination d0_0_20 + d1_1_20 + d1_3_23 + d2_5_23 + d3_3_20 + i5 +
        ((-2 : R) * X 0 4) * htwo + ((-1 : R) * X 5 12) * htwo + ((1 : R) * X 5 13) * htwo +
        ((-3 : R) * X 16 23) * htwo)
  · exact (show X 5 14 = 0 by
      linear_combination d4_0_14 + i3 + ((-2 : R) * X 0 6) * htwo + ((2 : R) * X 5 14) * htwo)
  · exact (show X 5 15 = 0 by linear_combination d1_5_25 + ((-1 : R) * X 5 15) * htwo)
  · exact (show X 5 16 = 0 by
      linear_combination d4_0_16 + i2 + ((-2 : R) * X 0 8) * htwo + ((2 : R) * X 5 16) * htwo)
  · exact (show X 5 17 = 0 by
      linear_combination c5 + d4_0_17 + ((-2 : R) * X 0 9) * htwo + ((2 : R) * X 5 17) * htwo)
  · exact (show X 5 18 = 0 by linear_combination d4_0_18 + ((2 : R) * X 5 18) * htwo)
  · exact (show X 5 19 = 0 by
      linear_combination c3 + d4_0_19 + ((-2 : R) * X 0 11) * htwo + ((2 : R) * X 5 19) * htwo)
  · exact (show X 5 20 = 0 by linear_combination d4_0_20 + ((2 : R) * X 5 20) * htwo)
  · exact (show X 5 21 = 0 by
      linear_combination d4_0_21 + i0 + ((-1 : R) * X 0 12) * htwo + ((2 : R) * X 5 21) * htwo)
  · exact (show X 5 22 = 0 by linear_combination d4_0_22 + ((2 : R) * X 5 22) * htwo)
  · exact (show X 5 23 = 0 by linear_combination d4_0_23 + ((2 : R) * X 5 23) * htwo)
  · exact (show X 5 24 = 0 by
      linear_combination c0 + d4_0_24 + ((-2 : R) * X 0 18) * htwo + ((2 : R) * X 5 24) * htwo)
  · exact (show X 5 25 = 0 by linear_combination d9_2_25 + ((-1 : R) * X 5 25) * htwo)

/-- Every entry of the `6`th row of a derivation all of whose coordinates vanish
is zero. -/
theorem entry_row_6 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hq : ∀ p, quotientCoordinate p X = 0) (hi : ∀ a, X (idealRow a) (idealCol a) = 0)
    (n : Fin 26) : X 6 n = 0 := by
  have htwo : (2 : R) = 0 := by exact_mod_cast CharP.cast_eq_zero R 2
  have hc := quotientCoordinate_entries hq
  have i22 : X 6 0 = 0 := hi 22
  have c19 : ((1 : ℤ) : R) * X 6 1 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 19
  have d1_6_14 : X 6 2 * ((-3 : ℤ) : R) + X 6 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 14 + ((0 : ℤ) : R) * X 0 14) =
      ((3 : ℤ) : R) * X 4 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 6 14
  have i18 : X 4 1 = 0 := hi 18
  have d1_6_16 : X 6 3 * ((-3 : ℤ) : R) + X 6 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 16 + ((0 : ℤ) : R) * X 0 16) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 6 16
  have d1_6_18 : X 6 4 * ((-3 : ℤ) : R) + X 6 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 18 + ((0 : ℤ) : R) * X 0 18) =
      ((-3 : ℤ) : R) * X 2 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 6 18
  have i14 : X 2 1 = 0 := hi 14
  have c15 : ((1 : ℤ) : R) * X 4 3 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 15
  have d1_4_16 : X 4 3 * ((-3 : ℤ) : R) + X 4 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 18 16 + ((0 : ℤ) : R) * X 0 16) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 4 16
  have d2_6_16 : X 6 5 * ((-3 : ℤ) : R) + X 6 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 18 16 + ((0 : ℤ) : R) * X 0 16) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 6 16
  have c12 : ((1 : ℤ) : R) * X 0 0 + ((1 : ℤ) : R) * X 11 11 = 0 := hc 12
  have c13 : ((1 : ℤ) : R) * X 0 0 + ((1 : ℤ) : R) * X 7 7 = 0 := hc 13
  have d0_5_21 : X 5 5 * ((3 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 21 21 + ((0 : ℤ) : R) * X 0 21) =
      ((3 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 5 21
  have d0_8_23 : X 8 8 * ((3 : ℤ) : R) + X 8 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 23 23 + ((0 : ℤ) : R) * X 0 23) =
      ((3 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 8 23
  have d1_0_10 : X 0 0 * ((-3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 10 10 + ((0 : ℤ) : R) * X 0 10) =
      ((-3 : ℤ) : R) * X 1 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 0 10
  have d1_3_16 : X 3 3 * ((-3 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 16 16 + ((0 : ℤ) : R) * X 0 16) =
      ((-3 : ℤ) : R) * X 1 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 3 16
  have d1_7_21 : X 7 7 * ((3 : ℤ) : R) + X 7 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 21 21 + ((0 : ℤ) : R) * X 0 21) =
      ((3 : ℤ) : R) * X 1 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 7 21
  have d1_11_23 : X 11 11 * ((3 : ℤ) : R) + X 11 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 23 23 + ((0 : ℤ) : R) * X 0 23) =
      ((3 : ℤ) : R) * X 1 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 11 23
  have d2_0_8 : X 0 0 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 8 8 + ((0 : ℤ) : R) * X 0 8) =
      ((3 : ℤ) : R) * X 2 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 0 8
  have d2_5_16 : X 5 5 * ((-3 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 16 16 + ((0 : ℤ) : R) * X 0 16) =
      ((-3 : ℤ) : R) * X 2 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 5 16
  have d3_0_6 : X 0 0 * ((-3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 6 6 + ((0 : ℤ) : R) * X 0 6) =
      ((-3 : ℤ) : R) * X 3 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 0 6
  have i12 : X 10 10 = 0 := hi 12
  have i13 : X 0 0 = 0 := hi 13
  have d1_6_21 : X 6 7 * ((3 : ℤ) : R) + X 6 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 21 + ((0 : ℤ) : R) * X 0 21) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 6 21
  have c11 : ((1 : ℤ) : R) * X 2 3 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 11
  have d3_0_8 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 6 8 + ((0 : ℤ) : R) * X 0 8) =
      ((3 : ℤ) : R) * X 2 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 0 8
  have d1_6_22 : X 6 9 * ((3 : ℤ) : R) + X 6 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 22 + ((0 : ℤ) : R) * X 0 22) =
      ((3 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 6 22
  have i10 : X 0 1 = 0 := hi 10
  have d3_0_10 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 6 10 + ((0 : ℤ) : R) * X 0 10) =
      ((-3 : ℤ) : R) * X 1 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 0 10
  have i9 : X 1 3 = 0 := hi 9
  have d1_6_23 : X 6 11 * ((3 : ℤ) : R) + X 6 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 23 + ((0 : ℤ) : R) * X 0 23) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 6 23
  have d3_0_12 : X 0 3 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 6 12 + ((0 : ℤ) : R) * X 0 12) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 0 12
  have i6 : X 0 3 = 0 := hi 6
  have d1_6_24 : X 6 12 * ((1 : ℤ) : R) + X 6 13 * ((1 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 6 24
  have d3_0_14 : X 0 5 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 6 14 + ((0 : ℤ) : R) * X 0 14) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 0 14
  have i4 : X 0 5 = 0 := hi 4
  have d1_6_25 : X 6 15 * ((3 : ℤ) : R) + X 6 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 6 25
  have d3_0_16 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 6 16 + ((0 : ℤ) : R) * X 0 16) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 0 16
  have c7 : ((1 : ℤ) : R) * X 0 7 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 7
  have d3_0_17 : X 0 7 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 6 17 + ((0 : ℤ) : R) * X 0 17) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 0 17
  have d3_0_18 : X 0 8 * ((-3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 6 18 + ((0 : ℤ) : R) * X 0 18) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 0 18
  have i2 : X 0 8 = 0 := hi 2
  have d3_0_19 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 6 19 + ((0 : ℤ) : R) * X 0 19) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 0 19
  have c3 : ((1 : ℤ) : R) * X 0 11 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 3
  have d3_0_20 : X 0 11 * ((-3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 6 20 + ((0 : ℤ) : R) * X 0 20) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 0 20
  have d3_0_21 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 6 21 + ((0 : ℤ) : R) * X 0 21) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 0 21
  have d3_0_22 : X 0 12 * ((-2 : ℤ) : R) + X 0 13 * ((1 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 6 22 + ((0 : ℤ) : R) * X 0 22) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 0 22
  have i0 : X 0 13 = 0 := hi 0
  have d3_0_23 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 6 23 + ((0 : ℤ) : R) * X 0 23) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 0 23
  have c1 : ((1 : ℤ) : R) * X 0 16 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 1
  have d3_0_24 : X 0 16 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 6 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 0 24
  have d7_2_25 : X 2 0 * ((0 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 6 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 7 + ((0 : ℤ) : R) * X 0 7 :=
    hX.entry 7 2 25
  fin_cases n
  · exact (show X 6 0 = 0 by linear_combination i22)
  · exact (show X 6 1 = 0 by linear_combination c19)
  · exact (show X 6 2 = 0 by
      linear_combination d1_6_14 + i18 + ((1 : R) * X 4 1) * htwo + ((2 : R) * X 6 2) * htwo)
  · exact (show X 6 3 = 0 by linear_combination d1_6_16 + ((2 : R) * X 6 3) * htwo)
  · exact (show X 6 4 = 0 by
      linear_combination d1_6_18 + i14 + ((-2 : R) * X 2 1) * htwo + ((2 : R) * X 6 4) * htwo)
  · exact (show X 6 5 = 0 by
      linear_combination c15 + d1_4_16 + d2_6_16 + ((1 : R) * X 4 3) * htwo +
        ((2 : R) * X 6 5) * htwo + ((-3 : R) * X 18 16) * htwo)
  · exact (show X 6 6 = 0 by
      linear_combination c12 + c13 + d0_5_21 + d0_8_23 + d1_0_10 + d1_3_16 + d1_7_21 + d1_11_23 +
        d2_0_8 + d2_5_16 + d3_0_6 + i12 + i13 + ((3 : R) * X 0 0) * htwo +
        ((-1 : R) * X 6 6) * htwo + ((-2 : R) * X 7 7) * htwo + ((-2 : R) * X 10 10) * htwo +
        ((-2 : R) * X 11 11) * htwo + ((-3 : R) * X 16 16) * htwo + ((3 : R) * X 21 21) * htwo +
        ((3 : R) * X 23 23) * htwo)
  · exact (show X 6 7 = 0 by linear_combination d1_6_21 + ((-1 : R) * X 6 7) * htwo)
  · exact (show X 6 8 = 0 by
      linear_combination c11 + d3_0_8 + ((1 : R) * X 2 3) * htwo + ((-1 : R) * X 6 8) * htwo)
  · exact (show X 6 9 = 0 by
      linear_combination d1_6_22 + i10 + ((1 : R) * X 0 1) * htwo + ((-1 : R) * X 6 9) * htwo)
  · exact (show X 6 10 = 0 by
      linear_combination d3_0_10 + i9 + ((-2 : R) * X 1 3) * htwo + ((-1 : R) * X 6 10) * htwo)
  · exact (show X 6 11 = 0 by linear_combination d1_6_23 + ((-1 : R) * X 6 11) * htwo)
  · exact (show X 6 12 = 0 by
      linear_combination d3_0_12 + i6 + ((-2 : R) * X 0 3) * htwo + ((-1 : R) * X 6 12) * htwo)
  · exact (show X 6 13 = 0 by
      linear_combination d1_6_24 + d3_0_12 + i6 + ((-2 : R) * X 0 3) * htwo +
        ((-2 : R) * X 6 12) * htwo)
  · exact (show X 6 14 = 0 by
      linear_combination d3_0_14 + i4 + ((-2 : R) * X 0 5) * htwo + ((-1 : R) * X 6 14) * htwo)
  · exact (show X 6 15 = 0 by linear_combination d1_6_25 + ((-1 : R) * X 6 15) * htwo)
  · exact (show X 6 16 = 0 by linear_combination d3_0_16 + ((-1 : R) * X 6 16) * htwo)
  · exact (show X 6 17 = 0 by
      linear_combination c7 + d3_0_17 + ((-2 : R) * X 0 7) * htwo + ((-1 : R) * X 6 17) * htwo)
  · exact (show X 6 18 = 0 by
      linear_combination d3_0_18 + i2 + ((1 : R) * X 0 8) * htwo + ((-1 : R) * X 6 18) * htwo)
  · exact (show X 6 19 = 0 by linear_combination d3_0_19 + ((-1 : R) * X 6 19) * htwo)
  · exact (show X 6 20 = 0 by
      linear_combination c3 + d3_0_20 + ((1 : R) * X 0 11) * htwo + ((-1 : R) * X 6 20) * htwo)
  · exact (show X 6 21 = 0 by linear_combination d3_0_21 + ((-1 : R) * X 6 21) * htwo)
  · exact (show X 6 22 = 0 by
      linear_combination d3_0_22 + i0 + ((1 : R) * X 0 12) * htwo + ((-1 : R) * X 0 13) * htwo +
        ((-1 : R) * X 6 22) * htwo)
  · exact (show X 6 23 = 0 by linear_combination d3_0_23 + ((-1 : R) * X 6 23) * htwo)
  · exact (show X 6 24 = 0 by
      linear_combination c1 + d3_0_24 + ((-2 : R) * X 0 16) * htwo + ((-1 : R) * X 6 24) * htwo)
  · exact (show X 6 25 = 0 by linear_combination d7_2_25 + ((2 : R) * X 6 25) * htwo)

end TauCeti.F4ShortRoot
