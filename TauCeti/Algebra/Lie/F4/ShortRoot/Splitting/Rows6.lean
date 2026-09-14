/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.IdealCoordinate

/-!
# Rows 21 to 23 of a derivation with vanishing coordinates

A matrix differentiating the invariant symmetric multiplication of the twenty-six-dimensional
module of type `F₄` modulo two, and annihilated by the twenty-six short-root quotient coordinates
and by the twenty-six ideal coordinates, is zero. This file proves that for the entries in rows
21 to 23.

The derivation equations are graded by the weight of the entry they constrain, so each entry is
determined by the few equations of its own weight together with the vanishing coordinates of that
weight; the proof of each entry is that combination. The equations themselves are the entrywise
form `TauCeti.F4ShortRoot.IsDerivation.entry` of the derivation equations, instantiated at the
relevant indices, and each combination is exact up to multiples of two, which vanish in
characteristic two.

## Main results

* `TauCeti.F4ShortRoot.entry_row_21` and its companions up to
  `TauCeti.F4ShortRoot.entry_row_23`: the entries of these rows vanish.
-/

public section

open Matrix

namespace TauCeti.F4ShortRoot

universe u

variable {R : Type u} [CommRing R] [CharP R 2]

/-- Every entry of the `21`th row of a derivation all of whose coordinates vanish
is zero. -/
theorem entry_row_21 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hq : ∀ p, quotientCoordinate p X = 0) (hi : ∀ a, X (idealRow a) (idealCol a) = 0)
    (n : Fin 26) : X 21 n = 0 := by
  have htwo : (2 : R) = 0 := by exact_mod_cast CharP.cast_eq_zero R 2
  have hc := quotientCoordinate_entries hq
  have d0_7_1 : X 7 0 * ((0 : ℤ) : R) + X 7 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1) =
      ((3 : ℤ) : R) * X 21 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 7 1
  have d0_5_1 : X 5 0 * ((0 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 21 1 + ((0 : ℤ) : R) * X 0 1) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 5 1
  have c24 : ((1 : ℤ) : R) * X 16 0 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 24
  have d0_5_2 : X 5 0 * ((0 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 21 2 + ((0 : ℤ) : R) * X 0 2) =
      ((-3 : ℤ) : R) * X 16 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 5 2
  have c23 : ((1 : ℤ) : R) * X 14 0 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 23
  have d0_5_3 : X 5 0 * ((0 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 21 3 + ((0 : ℤ) : R) * X 0 3) =
      ((3 : ℤ) : R) * X 14 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 5 3
  have d0_5_4 : X 5 0 * ((0 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 21 4 + ((0 : ℤ) : R) * X 0 4) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 5 4
  have d0_21_21 : X 21 5 * ((3 : ℤ) : R) + X 21 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 21 + ((0 : ℤ) : R) * X 0 21) =
      ((3 : ℤ) : R) * X 12 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 21 21
  have i25 : X 12 0 = 0 := hi 25
  have d0_5_6 : X 5 0 * ((0 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 21 6 + ((0 : ℤ) : R) * X 0 6) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 5 6
  have d0_5_7 : X 5 0 * ((0 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 21 7 + ((0 : ℤ) : R) * X 0 7) =
      ((3 : ℤ) : R) * X 10 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 5 7
  have i24 : X 10 0 = 0 := hi 24
  have d0_5_8 : X 5 0 * ((0 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 21 8 + ((0 : ℤ) : R) * X 0 8) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 5 8
  have d0_5_9 : X 5 0 * ((0 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 21 9 + ((0 : ℤ) : R) * X 0 9) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 5 9
  have c18 : ((1 : ℤ) : R) * X 7 0 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 18
  have d0_5_10 : X 5 0 * ((0 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 21 10 + ((0 : ℤ) : R) * X 0 10) =
      ((3 : ℤ) : R) * X 7 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 5 10
  have d0_5_11 : X 5 0 * ((0 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 21 11 + ((0 : ℤ) : R) * X 0 11) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 5 11
  have d0_5_12 : X 5 0 * ((0 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 21 12 + ((0 : ℤ) : R) * X 0 12) =
      ((-3 : ℤ) : R) * X 5 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 5 12
  have i21 : X 5 0 = 0 := hi 21
  have d0_5_13 : X 5 0 * ((3 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 21 13 + ((0 : ℤ) : R) * X 0 13) =
      ((-3 : ℤ) : R) * X 5 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 5 13
  have d0_5_14 : X 5 0 * ((0 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 21 14 + ((0 : ℤ) : R) * X 0 14) =
      ((3 : ℤ) : R) * X 3 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 5 14
  have i19 : X 3 0 = 0 := hi 19
  have c16 : ((1 : ℤ) : R) * X 5 1 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 16
  have d0_5_15 : X 5 1 * ((3 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 21 15 + ((0 : ℤ) : R) * X 0 15) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 5 15
  have d0_5_16 : X 5 0 * ((0 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 21 16 + ((0 : ℤ) : R) * X 0 16) =
      ((-3 : ℤ) : R) * X 2 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 5 16
  have i17 : X 2 0 = 0 := hi 17
  have d0_5_17 : X 5 2 * ((3 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 21 17 + ((0 : ℤ) : R) * X 0 17) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 5 17
  have d1_5_14 : X 5 2 * ((-3 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 14 + ((0 : ℤ) : R) * X 0 14) =
      ((3 : ℤ) : R) * X 3 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 5 14
  have i16 : X 3 1 = 0 := hi 16
  have d0_5_18 : X 5 0 * ((0 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 21 18 + ((0 : ℤ) : R) * X 0 18) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 5 18
  have d0_5_19 : X 5 3 * ((3 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 21 19 + ((0 : ℤ) : R) * X 0 19) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 5 19
  have d1_5_16 : X 5 3 * ((-3 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 16 + ((0 : ℤ) : R) * X 0 16) =
      ((-3 : ℤ) : R) * X 2 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 5 16
  have i14 : X 2 1 = 0 := hi 14
  have d1_7_20 : X 7 0 * ((0 : ℤ) : R) + X 7 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 21 20 + ((0 : ℤ) : R) * X 0 20) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 7 20
  have c13 : ((1 : ℤ) : R) * X 0 0 + ((1 : ℤ) : R) * X 7 7 = 0 := hc 13
  have d1_0_10 : X 0 0 * ((-3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 10 10 + ((0 : ℤ) : R) * X 0 10) =
      ((-3 : ℤ) : R) * X 1 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 0 10
  have d1_7_21 : X 7 7 * ((3 : ℤ) : R) + X 7 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 21 21 + ((0 : ℤ) : R) * X 0 21) =
      ((3 : ℤ) : R) * X 1 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 7 21
  have i12 : X 10 10 = 0 := hi 12
  have c10 : ((1 : ℤ) : R) * X 3 4 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 10
  have d0_5_22 : X 5 6 * ((3 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 21 22 + ((0 : ℤ) : R) * X 0 22) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 5 22
  have d1_3_18 : X 3 4 * ((-3 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 16 18 + ((0 : ℤ) : R) * X 0 18) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 3 18
  have d2_5_18 : X 5 6 * ((-3 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 16 18 + ((0 : ℤ) : R) * X 0 18) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 5 18
  have c8 : ((1 : ℤ) : R) * X 2 4 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 8
  have d0_5_23 : X 5 8 * ((3 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 21 23 + ((0 : ℤ) : R) * X 0 23) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 5 23
  have d1_2_18 : X 2 4 * ((-3 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 14 18 + ((0 : ℤ) : R) * X 0 18) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 2 18
  have d3_5_18 : X 5 8 * ((-3 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 14 18 + ((0 : ℤ) : R) * X 0 18) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 5 18
  have d0_5_24 : X 5 10 * ((3 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 21 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 5 24
  have d4_0_10 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 5 10 + ((0 : ℤ) : R) * X 0 10) =
      ((-3 : ℤ) : R) * X 1 4 + ((0 : ℤ) : R) * X 0 4 :=
    hX.entry 4 0 10
  have i7 : X 1 4 = 0 := hi 7
  have d0_0_20 : X 0 4 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 13 20 + ((0 : ℤ) : R) * X 0 20) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 0 20
  have d0_5_25 : X 5 12 * ((-1 : ℤ) : R) + X 5 13 * ((2 : ℤ) : R) -
        (((3 : ℤ) : R) * X 21 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 5 25
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
  fin_cases n
  · exact (show X 21 0 = 0 by linear_combination d0_7_1 + ((2 : R) * X 21 0) * htwo)
  · exact (show X 21 1 = 0 by linear_combination d0_5_1 + ((2 : R) * X 21 1) * htwo)
  · exact (show X 21 2 = 0 by
      linear_combination c24 + d0_5_2 + ((-2 : R) * X 16 0) * htwo + ((2 : R) * X 21 2) * htwo)
  · exact (show X 21 3 = 0 by
      linear_combination c23 + d0_5_3 + ((1 : R) * X 14 0) * htwo + ((2 : R) * X 21 3) * htwo)
  · exact (show X 21 4 = 0 by linear_combination d0_5_4 + ((2 : R) * X 21 4) * htwo)
  · exact (show X 21 5 = 0 by
      linear_combination d0_21_21 + i25 + ((1 : R) * X 12 0) * htwo +
        ((-1 : R) * X 21 5) * htwo)
  · exact (show X 21 6 = 0 by linear_combination d0_5_6 + ((2 : R) * X 21 6) * htwo)
  · exact (show X 21 7 = 0 by
      linear_combination d0_5_7 + i24 + ((1 : R) * X 10 0) * htwo + ((2 : R) * X 21 7) * htwo)
  · exact (show X 21 8 = 0 by linear_combination d0_5_8 + ((2 : R) * X 21 8) * htwo)
  · exact (show X 21 9 = 0 by linear_combination d0_5_9 + ((2 : R) * X 21 9) * htwo)
  · exact (show X 21 10 = 0 by
      linear_combination c18 + d0_5_10 + ((1 : R) * X 7 0) * htwo + ((2 : R) * X 21 10) * htwo)
  · exact (show X 21 11 = 0 by linear_combination d0_5_11 + ((2 : R) * X 21 11) * htwo)
  · exact (show X 21 12 = 0 by
      linear_combination d0_5_12 + i21 + ((-2 : R) * X 5 0) * htwo + ((2 : R) * X 21 12) * htwo)
  · exact (show X 21 13 = 0 by
      linear_combination d0_5_13 + ((-3 : R) * X 5 0) * htwo + ((2 : R) * X 21 13) * htwo)
  · exact (show X 21 14 = 0 by
      linear_combination d0_5_14 + i19 + ((1 : R) * X 3 0) * htwo + ((2 : R) * X 21 14) * htwo)
  · exact (show X 21 15 = 0 by
      linear_combination c16 + d0_5_15 + ((-2 : R) * X 5 1) * htwo + ((2 : R) * X 21 15) * htwo)
  · exact (show X 21 16 = 0 by
      linear_combination d0_5_16 + i17 + ((-2 : R) * X 2 0) * htwo + ((2 : R) * X 21 16) * htwo)
  · exact (show X 21 17 = 0 by
      linear_combination d0_5_17 + d1_5_14 + i16 + ((1 : R) * X 3 1) * htwo +
        ((2 : R) * X 21 17) * htwo)
  · exact (show X 21 18 = 0 by linear_combination d0_5_18 + ((2 : R) * X 21 18) * htwo)
  · exact (show X 21 19 = 0 by
      linear_combination d0_5_19 + d1_5_16 + i14 + ((-2 : R) * X 2 1) * htwo +
        ((2 : R) * X 21 19) * htwo)
  · exact (show X 21 20 = 0 by linear_combination d1_7_20 + ((2 : R) * X 21 20) * htwo)
  · exact (show X 21 21 = 0 by
      linear_combination c13 + d1_0_10 + d1_7_21 + i12 + ((1 : R) * X 0 0) * htwo +
        ((-2 : R) * X 7 7) * htwo + ((-2 : R) * X 10 10) * htwo + ((2 : R) * X 21 21) * htwo)
  · exact (show X 21 22 = 0 by
      linear_combination c10 + d0_5_22 + d1_3_18 + d2_5_18 + ((1 : R) * X 3 4) * htwo +
        ((-3 : R) * X 16 18) * htwo + ((2 : R) * X 21 22) * htwo)
  · exact (show X 21 23 = 0 by
      linear_combination c8 + d0_5_23 + d1_2_18 + d3_5_18 + ((1 : R) * X 2 4) * htwo +
        ((2 : R) * X 21 23) * htwo)
  · exact (show X 21 24 = 0 by
      linear_combination d0_5_24 + d4_0_10 + i7 + ((-2 : R) * X 1 4) * htwo +
        ((2 : R) * X 21 24) * htwo)
  · exact (show X 21 25 = 0 by
      linear_combination d0_0_20 + d0_5_25 + d1_1_20 + d1_3_23 + d1_5_24 + d2_5_23 + d3_3_20 +
        i5 + ((-2 : R) * X 0 4) * htwo + ((-1 : R) * X 5 12) * htwo +
        ((-1 : R) * X 5 13) * htwo + ((-3 : R) * X 16 23) * htwo + ((2 : R) * X 21 25) * htwo)

/-- Every entry of the `22`th row of a derivation all of whose coordinates vanish
is zero. -/
theorem entry_row_22 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hq : ∀ p, quotientCoordinate p X = 0) (hi : ∀ a, X (idealRow a) (idealCol a) = 0)
    (n : Fin 26) : X 22 n = 0 := by
  have htwo : (2 : R) = 0 := by exact_mod_cast CharP.cast_eq_zero R 2
  have hc := quotientCoordinate_entries hq
  have d0_9_1 : X 9 0 * ((0 : ℤ) : R) + X 9 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1) =
      ((3 : ℤ) : R) * X 22 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 9 1
  have d0_6_1 : X 6 0 * ((0 : ℤ) : R) + X 6 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 22 1 + ((0 : ℤ) : R) * X 0 1) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 6 1
  have c25 : ((1 : ℤ) : R) * X 18 0 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 25
  have d0_6_2 : X 6 0 * ((0 : ℤ) : R) + X 6 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 22 2 + ((0 : ℤ) : R) * X 0 2) =
      ((-3 : ℤ) : R) * X 18 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 6 2
  have d0_6_3 : X 6 0 * ((0 : ℤ) : R) + X 6 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 22 3 + ((0 : ℤ) : R) * X 0 3) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 6 3
  have c23 : ((1 : ℤ) : R) * X 14 0 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 23
  have d0_6_4 : X 6 0 * ((0 : ℤ) : R) + X 6 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 22 4 + ((0 : ℤ) : R) * X 0 4) =
      ((3 : ℤ) : R) * X 14 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 6 4
  have d0_6_5 : X 6 0 * ((0 : ℤ) : R) + X 6 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 22 5 + ((0 : ℤ) : R) * X 0 5) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 6 5
  have d0_22_22 : X 22 6 * ((3 : ℤ) : R) + X 22 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 22 + ((0 : ℤ) : R) * X 0 22) =
      ((3 : ℤ) : R) * X 12 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 22 22
  have i25 : X 12 0 = 0 := hi 25
  have d0_6_7 : X 6 0 * ((0 : ℤ) : R) + X 6 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 22 7 + ((0 : ℤ) : R) * X 0 7) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 6 7
  have d0_6_8 : X 6 0 * ((0 : ℤ) : R) + X 6 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 22 8 + ((0 : ℤ) : R) * X 0 8) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 6 8
  have d0_6_9 : X 6 0 * ((0 : ℤ) : R) + X 6 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 22 9 + ((0 : ℤ) : R) * X 0 9) =
      ((3 : ℤ) : R) * X 10 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 6 9
  have i24 : X 10 0 = 0 := hi 24
  have c20 : ((1 : ℤ) : R) * X 9 0 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 20
  have d0_6_10 : X 6 0 * ((0 : ℤ) : R) + X 6 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 22 10 + ((0 : ℤ) : R) * X 0 10) =
      ((3 : ℤ) : R) * X 9 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 6 10
  have d0_6_11 : X 6 0 * ((0 : ℤ) : R) + X 6 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 22 11 + ((0 : ℤ) : R) * X 0 11) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 6 11
  have d0_6_12 : X 6 0 * ((0 : ℤ) : R) + X 6 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 22 12 + ((0 : ℤ) : R) * X 0 12) =
      ((-3 : ℤ) : R) * X 6 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 6 12
  have i22 : X 6 0 = 0 := hi 22
  have d0_6_13 : X 6 0 * ((3 : ℤ) : R) + X 6 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 22 13 + ((0 : ℤ) : R) * X 0 13) =
      ((-3 : ℤ) : R) * X 6 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 6 13
  have d0_6_14 : X 6 0 * ((0 : ℤ) : R) + X 6 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 22 14 + ((0 : ℤ) : R) * X 0 14) =
      ((3 : ℤ) : R) * X 4 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 6 14
  have i20 : X 4 0 = 0 := hi 20
  have c19 : ((1 : ℤ) : R) * X 6 1 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 19
  have d0_6_15 : X 6 1 * ((3 : ℤ) : R) + X 6 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 22 15 + ((0 : ℤ) : R) * X 0 15) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 6 15
  have d0_6_16 : X 6 0 * ((0 : ℤ) : R) + X 6 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 22 16 + ((0 : ℤ) : R) * X 0 16) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 6 16
  have d0_6_17 : X 6 2 * ((3 : ℤ) : R) + X 6 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 22 17 + ((0 : ℤ) : R) * X 0 17) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 6 17
  have d1_6_14 : X 6 2 * ((-3 : ℤ) : R) + X 6 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 14 + ((0 : ℤ) : R) * X 0 14) =
      ((3 : ℤ) : R) * X 4 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 6 14
  have i18 : X 4 1 = 0 := hi 18
  have d0_6_18 : X 6 0 * ((0 : ℤ) : R) + X 6 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 22 18 + ((0 : ℤ) : R) * X 0 18) =
      ((-3 : ℤ) : R) * X 2 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 6 18
  have i17 : X 2 0 = 0 := hi 17
  have d1_9_19 : X 9 0 * ((0 : ℤ) : R) + X 9 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 22 19 + ((0 : ℤ) : R) * X 0 19) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 9 19
  have d0_6_20 : X 6 4 * ((3 : ℤ) : R) + X 6 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 22 20 + ((0 : ℤ) : R) * X 0 20) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 6 20
  have d1_6_18 : X 6 4 * ((-3 : ℤ) : R) + X 6 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 18 + ((0 : ℤ) : R) * X 0 18) =
      ((-3 : ℤ) : R) * X 2 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 6 18
  have i14 : X 2 1 = 0 := hi 14
  have c15 : ((1 : ℤ) : R) * X 4 3 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 15
  have d0_6_21 : X 6 5 * ((3 : ℤ) : R) + X 6 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 22 21 + ((0 : ℤ) : R) * X 0 21) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 6 21
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
  have d0_6_22 : X 6 6 * ((3 : ℤ) : R) + X 6 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 22 22 + ((0 : ℤ) : R) * X 0 22) =
      ((3 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 6 22
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
  have c11 : ((1 : ℤ) : R) * X 2 3 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 11
  have d0_6_23 : X 6 8 * ((3 : ℤ) : R) + X 6 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 22 23 + ((0 : ℤ) : R) * X 0 23) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 6 23
  have d3_0_8 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 6 8 + ((0 : ℤ) : R) * X 0 8) =
      ((3 : ℤ) : R) * X 2 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 0 8
  have d0_6_24 : X 6 10 * ((3 : ℤ) : R) + X 6 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 22 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 6 24
  have d3_0_10 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 6 10 + ((0 : ℤ) : R) * X 0 10) =
      ((-3 : ℤ) : R) * X 1 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 0 10
  have i9 : X 1 3 = 0 := hi 9
  have d0_6_25 : X 6 12 * ((-1 : ℤ) : R) + X 6 13 * ((2 : ℤ) : R) -
        (((3 : ℤ) : R) * X 22 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 6 25
  have d3_0_12 : X 0 3 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 6 12 + ((0 : ℤ) : R) * X 0 12) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 0 12
  have i6 : X 0 3 = 0 := hi 6
  fin_cases n
  · exact (show X 22 0 = 0 by linear_combination d0_9_1 + ((2 : R) * X 22 0) * htwo)
  · exact (show X 22 1 = 0 by linear_combination d0_6_1 + ((2 : R) * X 22 1) * htwo)
  · exact (show X 22 2 = 0 by
      linear_combination c25 + d0_6_2 + ((-2 : R) * X 18 0) * htwo + ((2 : R) * X 22 2) * htwo)
  · exact (show X 22 3 = 0 by linear_combination d0_6_3 + ((2 : R) * X 22 3) * htwo)
  · exact (show X 22 4 = 0 by
      linear_combination c23 + d0_6_4 + ((1 : R) * X 14 0) * htwo + ((2 : R) * X 22 4) * htwo)
  · exact (show X 22 5 = 0 by linear_combination d0_6_5 + ((2 : R) * X 22 5) * htwo)
  · exact (show X 22 6 = 0 by
      linear_combination d0_22_22 + i25 + ((1 : R) * X 12 0) * htwo +
        ((-1 : R) * X 22 6) * htwo)
  · exact (show X 22 7 = 0 by linear_combination d0_6_7 + ((2 : R) * X 22 7) * htwo)
  · exact (show X 22 8 = 0 by linear_combination d0_6_8 + ((2 : R) * X 22 8) * htwo)
  · exact (show X 22 9 = 0 by
      linear_combination d0_6_9 + i24 + ((1 : R) * X 10 0) * htwo + ((2 : R) * X 22 9) * htwo)
  · exact (show X 22 10 = 0 by
      linear_combination c20 + d0_6_10 + ((1 : R) * X 9 0) * htwo + ((2 : R) * X 22 10) * htwo)
  · exact (show X 22 11 = 0 by linear_combination d0_6_11 + ((2 : R) * X 22 11) * htwo)
  · exact (show X 22 12 = 0 by
      linear_combination d0_6_12 + i22 + ((-2 : R) * X 6 0) * htwo + ((2 : R) * X 22 12) * htwo)
  · exact (show X 22 13 = 0 by
      linear_combination d0_6_13 + ((-3 : R) * X 6 0) * htwo + ((2 : R) * X 22 13) * htwo)
  · exact (show X 22 14 = 0 by
      linear_combination d0_6_14 + i20 + ((1 : R) * X 4 0) * htwo + ((2 : R) * X 22 14) * htwo)
  · exact (show X 22 15 = 0 by
      linear_combination c19 + d0_6_15 + ((-2 : R) * X 6 1) * htwo + ((2 : R) * X 22 15) * htwo)
  · exact (show X 22 16 = 0 by linear_combination d0_6_16 + ((2 : R) * X 22 16) * htwo)
  · exact (show X 22 17 = 0 by
      linear_combination d0_6_17 + d1_6_14 + i18 + ((1 : R) * X 4 1) * htwo +
        ((2 : R) * X 22 17) * htwo)
  · exact (show X 22 18 = 0 by
      linear_combination d0_6_18 + i17 + ((-2 : R) * X 2 0) * htwo + ((2 : R) * X 22 18) * htwo)
  · exact (show X 22 19 = 0 by linear_combination d1_9_19 + ((2 : R) * X 22 19) * htwo)
  · exact (show X 22 20 = 0 by
      linear_combination d0_6_20 + d1_6_18 + i14 + ((-2 : R) * X 2 1) * htwo +
        ((2 : R) * X 22 20) * htwo)
  · exact (show X 22 21 = 0 by
      linear_combination c15 + d0_6_21 + d1_4_16 + d2_6_16 + ((1 : R) * X 4 3) * htwo +
        ((-3 : R) * X 18 16) * htwo + ((2 : R) * X 22 21) * htwo)
  · exact (show X 22 22 = 0 by
      linear_combination c12 + c13 + d0_5_21 + d0_6_22 + d0_8_23 + d1_0_10 + d1_3_16 + d1_7_21 +
        d1_11_23 + d2_0_8 + d2_5_16 + d3_0_6 + i12 + ((5 : R) * X 0 0) * htwo +
        ((-3 : R) * X 6 6) * htwo + ((-2 : R) * X 7 7) * htwo + ((-2 : R) * X 10 10) * htwo +
        ((-2 : R) * X 11 11) * htwo + ((-3 : R) * X 16 16) * htwo + ((3 : R) * X 21 21) * htwo +
        ((2 : R) * X 22 22) * htwo + ((3 : R) * X 23 23) * htwo)
  · exact (show X 22 23 = 0 by
      linear_combination c11 + d0_6_23 + d3_0_8 + ((1 : R) * X 2 3) * htwo +
        ((-3 : R) * X 6 8) * htwo + ((2 : R) * X 22 23) * htwo)
  · exact (show X 22 24 = 0 by
      linear_combination d0_6_24 + d3_0_10 + i9 + ((-2 : R) * X 1 3) * htwo +
        ((-3 : R) * X 6 10) * htwo + ((2 : R) * X 22 24) * htwo)
  · exact (show X 22 25 = 0 by
      linear_combination d0_6_25 + d3_0_12 + i6 + ((-2 : R) * X 0 3) * htwo +
        ((-1 : R) * X 6 12) * htwo + ((-1 : R) * X 6 13) * htwo + ((2 : R) * X 22 25) * htwo)

/-- Every entry of the `23`th row of a derivation all of whose coordinates vanish
is zero. -/
theorem entry_row_23 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hq : ∀ p, quotientCoordinate p X = 0) (hi : ∀ a, X (idealRow a) (idealCol a) = 0)
    (n : Fin 26) : X 23 n = 0 := by
  have htwo : (2 : R) = 0 := by exact_mod_cast CharP.cast_eq_zero R 2
  have hc := quotientCoordinate_entries hq
  have d0_11_1 : X 11 0 * ((0 : ℤ) : R) + X 11 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1) =
      ((3 : ℤ) : R) * X 23 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 11 1
  have d0_8_1 : X 8 0 * ((0 : ℤ) : R) + X 8 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 23 1 + ((0 : ℤ) : R) * X 0 1) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 8 1
  have d0_8_2 : X 8 0 * ((0 : ℤ) : R) + X 8 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 23 2 + ((0 : ℤ) : R) * X 0 2) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 8 2
  have c25 : ((1 : ℤ) : R) * X 18 0 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 25
  have d0_8_3 : X 8 0 * ((0 : ℤ) : R) + X 8 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 23 3 + ((0 : ℤ) : R) * X 0 3) =
      ((-3 : ℤ) : R) * X 18 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 8 3
  have c24 : ((1 : ℤ) : R) * X 16 0 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 24
  have d0_8_4 : X 8 0 * ((0 : ℤ) : R) + X 8 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 23 4 + ((0 : ℤ) : R) * X 0 4) =
      ((3 : ℤ) : R) * X 16 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 8 4
  have d0_8_5 : X 8 0 * ((0 : ℤ) : R) + X 8 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 23 5 + ((0 : ℤ) : R) * X 0 5) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 8 5
  have d0_8_6 : X 8 0 * ((0 : ℤ) : R) + X 8 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 23 6 + ((0 : ℤ) : R) * X 0 6) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 8 6
  have d0_8_7 : X 8 0 * ((0 : ℤ) : R) + X 8 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 23 7 + ((0 : ℤ) : R) * X 0 7) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 8 7
  have d0_23_23 : X 23 8 * ((3 : ℤ) : R) + X 23 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 23 + ((0 : ℤ) : R) * X 0 23) =
      ((3 : ℤ) : R) * X 12 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 23 23
  have i25 : X 12 0 = 0 := hi 25
  have d0_8_9 : X 8 0 * ((0 : ℤ) : R) + X 8 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 23 9 + ((0 : ℤ) : R) * X 0 9) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 8 9
  have c22 : ((1 : ℤ) : R) * X 11 0 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 22
  have d0_8_10 : X 8 0 * ((0 : ℤ) : R) + X 8 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 23 10 + ((0 : ℤ) : R) * X 0 10) =
      ((3 : ℤ) : R) * X 11 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 8 10
  have d0_8_11 : X 8 0 * ((0 : ℤ) : R) + X 8 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 23 11 + ((0 : ℤ) : R) * X 0 11) =
      ((3 : ℤ) : R) * X 10 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 8 11
  have i24 : X 10 0 = 0 := hi 24
  have d0_8_12 : X 8 0 * ((0 : ℤ) : R) + X 8 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 23 12 + ((0 : ℤ) : R) * X 0 12) =
      ((-3 : ℤ) : R) * X 8 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 8 12
  have i23 : X 8 0 = 0 := hi 23
  have d0_8_13 : X 8 0 * ((3 : ℤ) : R) + X 8 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 23 13 + ((0 : ℤ) : R) * X 0 13) =
      ((-3 : ℤ) : R) * X 8 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 8 13
  have d0_8_14 : X 8 0 * ((0 : ℤ) : R) + X 8 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 23 14 + ((0 : ℤ) : R) * X 0 14) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 8 14
  have c21 : ((1 : ℤ) : R) * X 8 1 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 21
  have d0_8_15 : X 8 1 * ((3 : ℤ) : R) + X 8 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 23 15 + ((0 : ℤ) : R) * X 0 15) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 8 15
  have d0_8_16 : X 8 0 * ((0 : ℤ) : R) + X 8 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 23 16 + ((0 : ℤ) : R) * X 0 16) =
      ((3 : ℤ) : R) * X 4 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 8 16
  have i20 : X 4 0 = 0 := hi 20
  have d1_11_17 : X 11 0 * ((0 : ℤ) : R) + X 11 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 23 17 + ((0 : ℤ) : R) * X 0 17) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 11 17
  have d0_8_18 : X 8 0 * ((0 : ℤ) : R) + X 8 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 23 18 + ((0 : ℤ) : R) * X 0 18) =
      ((-3 : ℤ) : R) * X 3 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 8 18
  have i19 : X 3 0 = 0 := hi 19
  have d0_8_19 : X 8 3 * ((3 : ℤ) : R) + X 8 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 23 19 + ((0 : ℤ) : R) * X 0 19) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 8 19
  have d1_8_16 : X 8 3 * ((-3 : ℤ) : R) + X 8 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 16 + ((0 : ℤ) : R) * X 0 16) =
      ((3 : ℤ) : R) * X 4 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 8 16
  have i18 : X 4 1 = 0 := hi 18
  have d0_8_20 : X 8 4 * ((3 : ℤ) : R) + X 8 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 23 20 + ((0 : ℤ) : R) * X 0 20) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 8 20
  have d1_8_18 : X 8 4 * ((-3 : ℤ) : R) + X 8 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 18 + ((0 : ℤ) : R) * X 0 18) =
      ((-3 : ℤ) : R) * X 3 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 8 18
  have i16 : X 3 1 = 0 := hi 16
  have c17 : ((1 : ℤ) : R) * X 4 2 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 17
  have d0_8_21 : X 8 5 * ((3 : ℤ) : R) + X 8 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 23 21 + ((0 : ℤ) : R) * X 0 21) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 8 21
  have d2_0_5 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 8 5 + ((0 : ℤ) : R) * X 0 5) =
      ((3 : ℤ) : R) * X 4 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 0 5
  have c14 : ((1 : ℤ) : R) * X 3 2 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 14
  have d0_8_22 : X 8 6 * ((3 : ℤ) : R) + X 8 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 23 22 + ((0 : ℤ) : R) * X 0 22) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 8 22
  have d2_0_6 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 8 6 + ((0 : ℤ) : R) * X 0 6) =
      ((-3 : ℤ) : R) * X 3 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 0 6
  have c12 : ((1 : ℤ) : R) * X 0 0 + ((1 : ℤ) : R) * X 11 11 = 0 := hc 12
  have d1_0_10 : X 0 0 * ((-3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 10 10 + ((0 : ℤ) : R) * X 0 10) =
      ((-3 : ℤ) : R) * X 1 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 0 10
  have d1_11_23 : X 11 11 * ((3 : ℤ) : R) + X 11 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 23 23 + ((0 : ℤ) : R) * X 0 23) =
      ((3 : ℤ) : R) * X 1 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 11 23
  have i12 : X 10 10 = 0 := hi 12
  have d0_8_24 : X 8 10 * ((3 : ℤ) : R) + X 8 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 23 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 8 24
  have d2_0_10 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 8 10 + ((0 : ℤ) : R) * X 0 10) =
      ((-3 : ℤ) : R) * X 1 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 0 10
  have i11 : X 1 2 = 0 := hi 11
  have d0_8_25 : X 8 12 * ((-1 : ℤ) : R) + X 8 13 * ((2 : ℤ) : R) -
        (((3 : ℤ) : R) * X 23 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 8 25
  have d2_0_12 : X 0 2 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 8 12 + ((0 : ℤ) : R) * X 0 12) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 0 12
  have i8 : X 0 2 = 0 := hi 8
  fin_cases n
  · exact (show X 23 0 = 0 by linear_combination d0_11_1 + ((2 : R) * X 23 0) * htwo)
  · exact (show X 23 1 = 0 by linear_combination d0_8_1 + ((2 : R) * X 23 1) * htwo)
  · exact (show X 23 2 = 0 by linear_combination d0_8_2 + ((2 : R) * X 23 2) * htwo)
  · exact (show X 23 3 = 0 by
      linear_combination c25 + d0_8_3 + ((-2 : R) * X 18 0) * htwo + ((2 : R) * X 23 3) * htwo)
  · exact (show X 23 4 = 0 by
      linear_combination c24 + d0_8_4 + ((1 : R) * X 16 0) * htwo + ((2 : R) * X 23 4) * htwo)
  · exact (show X 23 5 = 0 by linear_combination d0_8_5 + ((2 : R) * X 23 5) * htwo)
  · exact (show X 23 6 = 0 by linear_combination d0_8_6 + ((2 : R) * X 23 6) * htwo)
  · exact (show X 23 7 = 0 by linear_combination d0_8_7 + ((2 : R) * X 23 7) * htwo)
  · exact (show X 23 8 = 0 by
      linear_combination d0_23_23 + i25 + ((1 : R) * X 12 0) * htwo +
        ((-1 : R) * X 23 8) * htwo)
  · exact (show X 23 9 = 0 by linear_combination d0_8_9 + ((2 : R) * X 23 9) * htwo)
  · exact (show X 23 10 = 0 by
      linear_combination c22 + d0_8_10 + ((1 : R) * X 11 0) * htwo + ((2 : R) * X 23 10) * htwo)
  · exact (show X 23 11 = 0 by
      linear_combination d0_8_11 + i24 + ((1 : R) * X 10 0) * htwo + ((2 : R) * X 23 11) * htwo)
  · exact (show X 23 12 = 0 by
      linear_combination d0_8_12 + i23 + ((-2 : R) * X 8 0) * htwo + ((2 : R) * X 23 12) * htwo)
  · exact (show X 23 13 = 0 by
      linear_combination d0_8_13 + ((-3 : R) * X 8 0) * htwo + ((2 : R) * X 23 13) * htwo)
  · exact (show X 23 14 = 0 by linear_combination d0_8_14 + ((2 : R) * X 23 14) * htwo)
  · exact (show X 23 15 = 0 by
      linear_combination c21 + d0_8_15 + ((-2 : R) * X 8 1) * htwo + ((2 : R) * X 23 15) * htwo)
  · exact (show X 23 16 = 0 by
      linear_combination d0_8_16 + i20 + ((1 : R) * X 4 0) * htwo + ((2 : R) * X 23 16) * htwo)
  · exact (show X 23 17 = 0 by linear_combination d1_11_17 + ((2 : R) * X 23 17) * htwo)
  · exact (show X 23 18 = 0 by
      linear_combination d0_8_18 + i19 + ((-2 : R) * X 3 0) * htwo + ((2 : R) * X 23 18) * htwo)
  · exact (show X 23 19 = 0 by
      linear_combination d0_8_19 + d1_8_16 + i18 + ((1 : R) * X 4 1) * htwo +
        ((2 : R) * X 23 19) * htwo)
  · exact (show X 23 20 = 0 by
      linear_combination d0_8_20 + d1_8_18 + i16 + ((-2 : R) * X 3 1) * htwo +
        ((2 : R) * X 23 20) * htwo)
  · exact (show X 23 21 = 0 by
      linear_combination c17 + d0_8_21 + d2_0_5 + ((1 : R) * X 4 2) * htwo +
        ((2 : R) * X 23 21) * htwo)
  · exact (show X 23 22 = 0 by
      linear_combination c14 + d0_8_22 + d2_0_6 + ((-2 : R) * X 3 2) * htwo +
        ((2 : R) * X 23 22) * htwo)
  · exact (show X 23 23 = 0 by
      linear_combination c12 + d1_0_10 + d1_11_23 + i12 + ((1 : R) * X 0 0) * htwo +
        ((-2 : R) * X 10 10) * htwo + ((-2 : R) * X 11 11) * htwo + ((2 : R) * X 23 23) * htwo)
  · exact (show X 23 24 = 0 by
      linear_combination d0_8_24 + d2_0_10 + i11 + ((-2 : R) * X 1 2) * htwo +
        ((2 : R) * X 23 24) * htwo)
  · exact (show X 23 25 = 0 by
      linear_combination d0_8_25 + d2_0_12 + i8 + ((-2 : R) * X 0 2) * htwo +
        ((2 : R) * X 8 12) * htwo + ((-1 : R) * X 8 13) * htwo + ((2 : R) * X 23 25) * htwo)

end TauCeti.F4ShortRoot
