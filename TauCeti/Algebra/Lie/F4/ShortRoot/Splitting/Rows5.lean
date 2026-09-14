/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.IdealCoordinate

/-!
# Rows 18 to 20 of a derivation with vanishing coordinates

A matrix differentiating the invariant symmetric multiplication of the twenty-six-dimensional
module of type `F₄` modulo two, and annihilated by the twenty-six short-root quotient coordinates
and by the twenty-six ideal coordinates, is zero. This file proves that for the entries in rows
18 to 20.

The derivation equations are graded by the weight of the entry they constrain, so each entry is
determined by the few equations of its own weight together with the vanishing coordinates of that
weight; the proof of each entry is that combination. The equations themselves are the entrywise
form `TauCeti.F4ShortRoot.IsDerivation.entry` of the derivation equations, instantiated at the
relevant indices, and each combination is exact up to multiples of two, which vanish in
characteristic two.

## Main results

* `TauCeti.F4ShortRoot.entry_row_18` and its companions up to
  `TauCeti.F4ShortRoot.entry_row_20`: the entries of these rows vanish.
-/

public section

open Matrix

namespace TauCeti.F4ShortRoot

universe u

variable {R : Type u} [CommRing R] [CharP R 2]

/-- Every entry of the `18`th row of a derivation all of whose coordinates vanish
is zero. -/
theorem entry_row_18 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hq : ∀ p, quotientCoordinate p X = 0) (hi : ∀ a, X (idealRow a) (idealCol a) = 0)
    (n : Fin 26) : X 18 n = 0 := by
  have htwo : (2 : R) = 0 := by exact_mod_cast CharP.cast_eq_zero R 2
  have hc := quotientCoordinate_entries hq
  have c25 : ((1 : ℤ) : R) * X 18 0 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 25
  have d0_18_15 : X 18 1 * ((3 : ℤ) : R) + X 18 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 15 + ((0 : ℤ) : R) * X 0 15) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 18 15
  have d0_18_17 : X 18 2 * ((3 : ℤ) : R) + X 18 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 17 + ((0 : ℤ) : R) * X 0 17) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 18 17
  have d0_18_19 : X 18 3 * ((3 : ℤ) : R) + X 18 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 19 + ((0 : ℤ) : R) * X 0 19) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 18 19
  have d0_18_20 : X 18 4 * ((3 : ℤ) : R) + X 18 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 20 + ((0 : ℤ) : R) * X 0 20) =
      ((-3 : ℤ) : R) * X 10 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 18 20
  have i24 : X 10 0 = 0 := hi 24
  have d0_18_21 : X 18 5 * ((3 : ℤ) : R) + X 18 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 21 + ((0 : ℤ) : R) * X 0 21) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 18 21
  have d0_18_22 : X 18 6 * ((3 : ℤ) : R) + X 18 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 22 + ((0 : ℤ) : R) * X 0 22) =
      ((3 : ℤ) : R) * X 8 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 18 22
  have i23 : X 8 0 = 0 := hi 23
  have d1_4_7 : X 4 0 * ((0 : ℤ) : R) + X 4 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 18 7 + ((0 : ℤ) : R) * X 0 7) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 4 7
  have d0_18_23 : X 18 8 * ((3 : ℤ) : R) + X 18 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 23 + ((0 : ℤ) : R) * X 0 23) =
      ((-3 : ℤ) : R) * X 6 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 18 23
  have i22 : X 6 0 = 0 := hi 22
  have c21 : ((1 : ℤ) : R) * X 8 1 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 21
  have d1_4_9 : X 4 0 * ((0 : ℤ) : R) + X 4 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 18 9 + ((0 : ℤ) : R) * X 0 9) =
      ((3 : ℤ) : R) * X 8 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 4 9
  have d0_18_24 : X 18 10 * ((3 : ℤ) : R) + X 18 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 24 + ((0 : ℤ) : R) * X 0 24) =
      ((3 : ℤ) : R) * X 4 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 18 24
  have i20 : X 4 0 = 0 := hi 20
  have c19 : ((1 : ℤ) : R) * X 6 1 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 19
  have d1_4_11 : X 4 0 * ((0 : ℤ) : R) + X 4 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 18 11 + ((0 : ℤ) : R) * X 0 11) =
      ((-3 : ℤ) : R) * X 6 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 4 11
  have d0_18_25 : X 18 12 * ((-1 : ℤ) : R) + X 18 13 * ((2 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 18 25
  have d1_4_13 : X 4 1 * ((-3 : ℤ) : R) + X 4 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 18 13 + ((0 : ℤ) : R) * X 0 13) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 4 13
  have i18 : X 4 1 = 0 := hi 18
  have c17 : ((1 : ℤ) : R) * X 4 2 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 17
  have d1_4_14 : X 4 2 * ((-3 : ℤ) : R) + X 4 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 18 14 + ((0 : ℤ) : R) * X 0 14) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 4 14
  have d1_4_15 : X 4 0 * ((0 : ℤ) : R) + X 4 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 18 15 + ((0 : ℤ) : R) * X 0 15) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 4 15
  have c15 : ((1 : ℤ) : R) * X 4 3 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 15
  have d1_4_16 : X 4 3 * ((-3 : ℤ) : R) + X 4 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 18 16 + ((0 : ℤ) : R) * X 0 16) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 4 16
  have d1_4_17 : X 4 0 * ((0 : ℤ) : R) + X 4 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 18 17 + ((0 : ℤ) : R) * X 0 17) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 4 17
  have c13 : ((1 : ℤ) : R) * X 0 0 + ((1 : ℤ) : R) * X 7 7 = 0 := hc 13
  have d0_5_21 : X 5 5 * ((3 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 21 21 + ((0 : ℤ) : R) * X 0 21) =
      ((3 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 5 21
  have d1_3_16 : X 3 3 * ((-3 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 16 16 + ((0 : ℤ) : R) * X 0 16) =
      ((-3 : ℤ) : R) * X 1 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 3 16
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
  have i13 : X 0 0 = 0 := hi 13
  have d1_4_19 : X 4 0 * ((0 : ℤ) : R) + X 4 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 18 19 + ((0 : ℤ) : R) * X 0 19) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 4 19
  have d1_4_20 : X 4 0 * ((0 : ℤ) : R) + X 4 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 18 20 + ((0 : ℤ) : R) * X 0 20) =
      ((3 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 4 20
  have i10 : X 0 1 = 0 := hi 10
  have d2_6_21 : X 6 0 * ((0 : ℤ) : R) + X 6 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 18 21 + ((0 : ℤ) : R) * X 0 21) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 6 21
  have d1_4_22 : X 4 9 * ((3 : ℤ) : R) + X 4 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 18 22 + ((0 : ℤ) : R) * X 0 22) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 4 22
  have d2_4_20 : X 4 9 * ((-3 : ℤ) : R) + X 4 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 20 + ((0 : ℤ) : R) * X 0 20) =
      ((3 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 4 20
  have i8 : X 0 2 = 0 := hi 8
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
  have d2_6_24 : X 6 14 * ((3 : ℤ) : R) + X 6 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 18 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 6 24
  have d3_0_14 : X 0 5 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 6 14 + ((0 : ℤ) : R) * X 0 14) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 0 14
  have i4 : X 0 5 = 0 := hi 4
  have c7 : ((1 : ℤ) : R) * X 0 7 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 7
  have d2_6_25 : X 6 17 * ((3 : ℤ) : R) + X 6 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 18 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 6 25
  have d3_0_17 : X 0 7 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 6 17 + ((0 : ℤ) : R) * X 0 17) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 0 17
  fin_cases n
  · exact (show X 18 0 = 0 by linear_combination c25)
  · exact (show X 18 1 = 0 by linear_combination d0_18_15 + ((-1 : R) * X 18 1) * htwo)
  · exact (show X 18 2 = 0 by linear_combination d0_18_17 + ((-1 : R) * X 18 2) * htwo)
  · exact (show X 18 3 = 0 by linear_combination d0_18_19 + ((-1 : R) * X 18 3) * htwo)
  · exact (show X 18 4 = 0 by
      linear_combination d0_18_20 + i24 + ((-2 : R) * X 10 0) * htwo +
        ((-1 : R) * X 18 4) * htwo)
  · exact (show X 18 5 = 0 by linear_combination d0_18_21 + ((-1 : R) * X 18 5) * htwo)
  · exact (show X 18 6 = 0 by
      linear_combination d0_18_22 + i23 + ((1 : R) * X 8 0) * htwo + ((-1 : R) * X 18 6) * htwo)
  · exact (show X 18 7 = 0 by linear_combination d1_4_7 + ((-1 : R) * X 18 7) * htwo)
  · exact (show X 18 8 = 0 by
      linear_combination d0_18_23 + i22 + ((-2 : R) * X 6 0) * htwo +
        ((-1 : R) * X 18 8) * htwo)
  · exact (show X 18 9 = 0 by
      linear_combination c21 + d1_4_9 + ((1 : R) * X 8 1) * htwo + ((-1 : R) * X 18 9) * htwo)
  · exact (show X 18 10 = 0 by
      linear_combination d0_18_24 + i20 + ((1 : R) * X 4 0) * htwo +
        ((-1 : R) * X 18 10) * htwo)
  · exact (show X 18 11 = 0 by
      linear_combination c19 + d1_4_11 + ((-2 : R) * X 6 1) * htwo +
        ((-1 : R) * X 18 11) * htwo)
  · exact (show X 18 12 = 0 by
      linear_combination d0_18_25 + ((1 : R) * X 18 12) * htwo + ((-1 : R) * X 18 13) * htwo)
  · exact (show X 18 13 = 0 by
      linear_combination d1_4_13 + i18 + ((1 : R) * X 4 1) * htwo + ((-1 : R) * X 18 13) * htwo)
  · exact (show X 18 14 = 0 by
      linear_combination c17 + d1_4_14 + ((1 : R) * X 4 2) * htwo + ((-1 : R) * X 18 14) * htwo)
  · exact (show X 18 15 = 0 by linear_combination d1_4_15 + ((-1 : R) * X 18 15) * htwo)
  · exact (show X 18 16 = 0 by
      linear_combination c15 + d1_4_16 + ((1 : R) * X 4 3) * htwo + ((-1 : R) * X 18 16) * htwo)
  · exact (show X 18 17 = 0 by linear_combination d1_4_17 + ((-1 : R) * X 18 17) * htwo)
  · exact (show X 18 18 = 0 by
      linear_combination c13 + d0_5_21 + d1_3_16 + d1_7_21 + d2_5_16 + d2_6_18 + d3_0_6 + i13 +
        ((2 : R) * X 0 0) * htwo + ((-3 : R) * X 2 2) * htwo + ((-2 : R) * X 7 7) * htwo +
        ((-3 : R) * X 16 16) * htwo + ((-1 : R) * X 18 18) * htwo + ((3 : R) * X 21 21) * htwo)
  · exact (show X 18 19 = 0 by linear_combination d1_4_19 + ((-1 : R) * X 18 19) * htwo)
  · exact (show X 18 20 = 0 by
      linear_combination d1_4_20 + i10 + ((1 : R) * X 0 1) * htwo + ((-1 : R) * X 18 20) * htwo)
  · exact (show X 18 21 = 0 by linear_combination d2_6_21 + ((-1 : R) * X 18 21) * htwo)
  · exact (show X 18 22 = 0 by
      linear_combination d1_4_22 + d2_4_20 + i8 + ((1 : R) * X 0 2) * htwo +
        ((-1 : R) * X 18 22) * htwo)
  · exact (show X 18 23 = 0 by
      linear_combination d1_6_24 + d2_6_23 + d3_0_12 + i6 + ((-2 : R) * X 0 3) * htwo +
        ((-3 : R) * X 6 12) * htwo + ((-1 : R) * X 18 23) * htwo)
  · exact (show X 18 24 = 0 by
      linear_combination d2_6_24 + d3_0_14 + i4 + ((-2 : R) * X 0 5) * htwo +
        ((-3 : R) * X 6 14) * htwo + ((-1 : R) * X 18 24) * htwo)
  · exact (show X 18 25 = 0 by
      linear_combination c7 + d2_6_25 + d3_0_17 + ((-2 : R) * X 0 7) * htwo +
        ((-3 : R) * X 6 17) * htwo + ((-1 : R) * X 18 25) * htwo)

/-- Every entry of the `19`th row of a derivation all of whose coordinates vanish
is zero. -/
theorem entry_row_19 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hq : ∀ p, quotientCoordinate p X = 0) (hi : ∀ a, X (idealRow a) (idealCol a) = 0)
    (n : Fin 26) : X 19 n = 0 := by
  have htwo : (2 : R) = 0 := by exact_mod_cast CharP.cast_eq_zero R 2
  have hc := quotientCoordinate_entries hq
  have d0_7_2 : X 7 0 * ((0 : ℤ) : R) + X 7 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2) =
      ((-3 : ℤ) : R) * X 19 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 7 2
  have c24 : ((1 : ℤ) : R) * X 16 0 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 24
  have d0_3_1 : X 3 0 * ((0 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 19 1 + ((0 : ℤ) : R) * X 0 1) =
      ((-3 : ℤ) : R) * X 16 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 3 1
  have d0_3_2 : X 3 0 * ((0 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 19 2 + ((0 : ℤ) : R) * X 0 2) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 3 2
  have d0_3_3 : X 3 0 * ((0 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 19 3 + ((0 : ℤ) : R) * X 0 3) =
      ((3 : ℤ) : R) * X 12 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 3 3
  have i25 : X 12 0 = 0 := hi 25
  have d0_3_4 : X 3 0 * ((0 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 19 4 + ((0 : ℤ) : R) * X 0 4) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 3 4
  have c22 : ((1 : ℤ) : R) * X 11 0 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 22
  have d0_3_5 : X 3 0 * ((0 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 19 5 + ((0 : ℤ) : R) * X 0 5) =
      ((-3 : ℤ) : R) * X 11 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 3 5
  have d0_3_6 : X 3 0 * ((0 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 19 6 + ((0 : ℤ) : R) * X 0 6) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 3 6
  have d0_3_7 : X 3 0 * ((0 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 19 7 + ((0 : ℤ) : R) * X 0 7) =
      ((3 : ℤ) : R) * X 8 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 3 7
  have i23 : X 8 0 = 0 := hi 23
  have c18 : ((1 : ℤ) : R) * X 7 0 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 18
  have d0_3_8 : X 3 0 * ((0 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 19 8 + ((0 : ℤ) : R) * X 0 8) =
      ((3 : ℤ) : R) * X 7 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 3 8
  have d0_3_9 : X 3 0 * ((0 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 19 9 + ((0 : ℤ) : R) * X 0 9) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 3 9
  have d0_3_10 : X 3 0 * ((0 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 19 10 + ((0 : ℤ) : R) * X 0 10) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 3 10
  have d0_3_11 : X 3 0 * ((0 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 19 11 + ((0 : ℤ) : R) * X 0 11) =
      ((-3 : ℤ) : R) * X 5 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 3 11
  have i21 : X 5 0 = 0 := hi 21
  have d0_3_12 : X 3 0 * ((0 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 19 12 + ((0 : ℤ) : R) * X 0 12) =
      ((3 : ℤ) : R) * X 3 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 3 12
  have i19 : X 3 0 = 0 := hi 19
  have d0_3_13 : X 3 0 * ((3 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 19 13 + ((0 : ℤ) : R) * X 0 13) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 3 13
  have d0_3_14 : X 3 0 * ((0 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 19 14 + ((0 : ℤ) : R) * X 0 14) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 3 14
  have d0_3_15 : X 3 1 * ((3 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 19 15 + ((0 : ℤ) : R) * X 0 15) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 3 15
  have i16 : X 3 1 = 0 := hi 16
  have d0_3_16 : X 3 0 * ((0 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 19 16 + ((0 : ℤ) : R) * X 0 16) =
      ((-3 : ℤ) : R) * X 1 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 3 16
  have i15 : X 1 0 = 0 := hi 15
  have c14 : ((1 : ℤ) : R) * X 3 2 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 14
  have d0_3_17 : X 3 2 * ((3 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 19 17 + ((0 : ℤ) : R) * X 0 17) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 3 17
  have d0_3_18 : X 3 0 * ((0 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 19 18 + ((0 : ℤ) : R) * X 0 18) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 3 18
  have c12 : ((1 : ℤ) : R) * X 0 0 + ((1 : ℤ) : R) * X 11 11 = 0 := hc 12
  have c13 : ((1 : ℤ) : R) * X 0 0 + ((1 : ℤ) : R) * X 7 7 = 0 := hc 13
  have d0_3_19 : X 3 3 * ((3 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 19 19 + ((0 : ℤ) : R) * X 0 19) =
      ((3 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 3 19
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
  have i12 : X 10 10 = 0 := hi 12
  have i13 : X 0 0 = 0 := hi 13
  have c10 : ((1 : ℤ) : R) * X 3 4 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 10
  have d0_3_20 : X 3 4 * ((3 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 19 20 + ((0 : ℤ) : R) * X 0 20) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 3 20
  have d0_3_21 : X 3 5 * ((3 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 19 21 + ((0 : ℤ) : R) * X 0 21) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 3 21
  have d2_3_16 : X 3 5 * ((-3 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 16 + ((0 : ℤ) : R) * X 0 16) =
      ((-3 : ℤ) : R) * X 1 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 3 16
  have i11 : X 1 2 = 0 := hi 11
  have d2_7_22 : X 7 0 * ((0 : ℤ) : R) + X 7 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 19 22 + ((0 : ℤ) : R) * X 0 22) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 7 22
  have d2_7_23 : X 7 12 * ((2 : ℤ) : R) + X 7 13 * ((-1 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 19 23 + ((0 : ℤ) : R) * X 0 23) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 7 23
  have d4_1_13 : X 1 0 * ((0 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 7 13 + ((0 : ℤ) : R) * X 0 13) =
      ((-3 : ℤ) : R) * X 1 4 + ((0 : ℤ) : R) * X 0 4 :=
    hX.entry 4 1 13
  have i7 : X 1 4 = 0 := hi 7
  have c6 : ((1 : ℤ) : R) * X 1 6 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 6
  have d2_7_24 : X 7 14 * ((3 : ℤ) : R) + X 7 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 19 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 7 24
  have d4_1_14 : X 1 6 * ((3 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 7 14 + ((0 : ℤ) : R) * X 0 14) =
      ((0 : ℤ) : R) * X 0 4 + ((0 : ℤ) : R) * X 0 4 :=
    hX.entry 4 1 14
  have d0_3_25 : X 3 12 * ((-1 : ℤ) : R) + X 3 13 * ((2 : ℤ) : R) -
        (((3 : ℤ) : R) * X 19 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 3 25
  have d6_0_12 : X 0 6 * ((-3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 3 12 + ((0 : ℤ) : R) * X 0 12) =
      ((0 : ℤ) : R) * X 0 6 + ((0 : ℤ) : R) * X 0 6 :=
    hX.entry 6 0 12
  have i3 : X 0 6 = 0 := hi 3
  fin_cases n
  · exact (show X 19 0 = 0 by linear_combination d0_7_2 + ((-1 : R) * X 19 0) * htwo)
  · exact (show X 19 1 = 0 by
      linear_combination c24 + d0_3_1 + ((-2 : R) * X 16 0) * htwo + ((2 : R) * X 19 1) * htwo)
  · exact (show X 19 2 = 0 by linear_combination d0_3_2 + ((2 : R) * X 19 2) * htwo)
  · exact (show X 19 3 = 0 by
      linear_combination d0_3_3 + i25 + ((1 : R) * X 12 0) * htwo + ((2 : R) * X 19 3) * htwo)
  · exact (show X 19 4 = 0 by linear_combination d0_3_4 + ((2 : R) * X 19 4) * htwo)
  · exact (show X 19 5 = 0 by
      linear_combination c22 + d0_3_5 + ((-2 : R) * X 11 0) * htwo + ((2 : R) * X 19 5) * htwo)
  · exact (show X 19 6 = 0 by linear_combination d0_3_6 + ((2 : R) * X 19 6) * htwo)
  · exact (show X 19 7 = 0 by
      linear_combination d0_3_7 + i23 + ((1 : R) * X 8 0) * htwo + ((2 : R) * X 19 7) * htwo)
  · exact (show X 19 8 = 0 by
      linear_combination c18 + d0_3_8 + ((1 : R) * X 7 0) * htwo + ((2 : R) * X 19 8) * htwo)
  · exact (show X 19 9 = 0 by linear_combination d0_3_9 + ((2 : R) * X 19 9) * htwo)
  · exact (show X 19 10 = 0 by linear_combination d0_3_10 + ((2 : R) * X 19 10) * htwo)
  · exact (show X 19 11 = 0 by
      linear_combination d0_3_11 + i21 + ((-2 : R) * X 5 0) * htwo + ((2 : R) * X 19 11) * htwo)
  · exact (show X 19 12 = 0 by
      linear_combination d0_3_12 + i19 + ((1 : R) * X 3 0) * htwo + ((2 : R) * X 19 12) * htwo)
  · exact (show X 19 13 = 0 by
      linear_combination d0_3_13 + i19 + ((-2 : R) * X 3 0) * htwo + ((2 : R) * X 19 13) * htwo)
  · exact (show X 19 14 = 0 by linear_combination d0_3_14 + ((2 : R) * X 19 14) * htwo)
  · exact (show X 19 15 = 0 by
      linear_combination d0_3_15 + i16 + ((-2 : R) * X 3 1) * htwo + ((2 : R) * X 19 15) * htwo)
  · exact (show X 19 16 = 0 by
      linear_combination d0_3_16 + i15 + ((-2 : R) * X 1 0) * htwo + ((2 : R) * X 19 16) * htwo)
  · exact (show X 19 17 = 0 by
      linear_combination c14 + d0_3_17 + ((-2 : R) * X 3 2) * htwo + ((2 : R) * X 19 17) * htwo)
  · exact (show X 19 18 = 0 by linear_combination d0_3_18 + ((2 : R) * X 19 18) * htwo)
  · exact (show X 19 19 = 0 by
      linear_combination c12 + c13 + d0_3_19 + d0_5_21 + d0_8_23 + d1_0_10 + d1_3_16 + d1_7_21 +
        d1_11_23 + d2_0_8 + d2_5_16 + i12 + i13 + ((3 : R) * X 0 0) * htwo +
        ((-2 : R) * X 7 7) * htwo + ((-2 : R) * X 10 10) * htwo + ((-2 : R) * X 11 11) * htwo +
        ((-3 : R) * X 16 16) * htwo + ((2 : R) * X 19 19) * htwo + ((3 : R) * X 21 21) * htwo +
        ((3 : R) * X 23 23) * htwo)
  · exact (show X 19 20 = 0 by
      linear_combination c10 + d0_3_20 + ((-2 : R) * X 3 4) * htwo + ((2 : R) * X 19 20) * htwo)
  · exact (show X 19 21 = 0 by
      linear_combination d0_3_21 + d2_3_16 + i11 + ((-2 : R) * X 1 2) * htwo +
        ((2 : R) * X 19 21) * htwo)
  · exact (show X 19 22 = 0 by linear_combination d2_7_22 + ((-1 : R) * X 19 22) * htwo)
  · exact (show X 19 23 = 0 by
      linear_combination d2_7_23 + d4_1_13 + i7 + ((-2 : R) * X 1 4) * htwo +
        ((-1 : R) * X 7 12) * htwo + ((2 : R) * X 7 13) * htwo + ((-1 : R) * X 19 23) * htwo)
  · exact (show X 19 24 = 0 by
      linear_combination c6 + d2_7_24 + d4_1_14 + ((-2 : R) * X 1 6) * htwo +
        ((-1 : R) * X 19 24) * htwo)
  · exact (show X 19 25 = 0 by
      linear_combination d0_3_25 + d6_0_12 + i3 + ((1 : R) * X 0 6) * htwo +
        ((-1 : R) * X 3 12) * htwo + ((-1 : R) * X 3 13) * htwo + ((2 : R) * X 19 25) * htwo)

/-- Every entry of the `20`th row of a derivation all of whose coordinates vanish
is zero. -/
theorem entry_row_20 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hq : ∀ p, quotientCoordinate p X = 0) (hi : ∀ a, X (idealRow a) (idealCol a) = 0)
    (n : Fin 26) : X 20 n = 0 := by
  have htwo : (2 : R) = 0 := by exact_mod_cast CharP.cast_eq_zero R 2
  have hc := quotientCoordinate_entries hq
  have d0_9_2 : X 9 0 * ((0 : ℤ) : R) + X 9 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2) =
      ((-3 : ℤ) : R) * X 20 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 9 2
  have c25 : ((1 : ℤ) : R) * X 18 0 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 25
  have d0_4_1 : X 4 0 * ((0 : ℤ) : R) + X 4 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 20 1 + ((0 : ℤ) : R) * X 0 1) =
      ((-3 : ℤ) : R) * X 18 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 4 1
  have d0_4_2 : X 4 0 * ((0 : ℤ) : R) + X 4 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 20 2 + ((0 : ℤ) : R) * X 0 2) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 4 2
  have d0_4_3 : X 4 0 * ((0 : ℤ) : R) + X 4 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 20 3 + ((0 : ℤ) : R) * X 0 3) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 4 3
  have d0_4_4 : X 4 0 * ((0 : ℤ) : R) + X 4 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 20 4 + ((0 : ℤ) : R) * X 0 4) =
      ((3 : ℤ) : R) * X 12 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 4 4
  have i25 : X 12 0 = 0 := hi 25
  have d0_4_5 : X 4 0 * ((0 : ℤ) : R) + X 4 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 20 5 + ((0 : ℤ) : R) * X 0 5) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 4 5
  have c22 : ((1 : ℤ) : R) * X 11 0 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 22
  have d0_4_6 : X 4 0 * ((0 : ℤ) : R) + X 4 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 20 6 + ((0 : ℤ) : R) * X 0 6) =
      ((-3 : ℤ) : R) * X 11 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 4 6
  have d0_4_7 : X 4 0 * ((0 : ℤ) : R) + X 4 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 20 7 + ((0 : ℤ) : R) * X 0 7) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 4 7
  have c20 : ((1 : ℤ) : R) * X 9 0 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 20
  have d0_4_8 : X 4 0 * ((0 : ℤ) : R) + X 4 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 20 8 + ((0 : ℤ) : R) * X 0 8) =
      ((3 : ℤ) : R) * X 9 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 4 8
  have d0_4_9 : X 4 0 * ((0 : ℤ) : R) + X 4 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 20 9 + ((0 : ℤ) : R) * X 0 9) =
      ((3 : ℤ) : R) * X 8 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 4 9
  have i23 : X 8 0 = 0 := hi 23
  have d0_4_10 : X 4 0 * ((0 : ℤ) : R) + X 4 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 20 10 + ((0 : ℤ) : R) * X 0 10) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 4 10
  have d0_4_11 : X 4 0 * ((0 : ℤ) : R) + X 4 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 20 11 + ((0 : ℤ) : R) * X 0 11) =
      ((-3 : ℤ) : R) * X 6 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 4 11
  have i22 : X 6 0 = 0 := hi 22
  have d0_4_12 : X 4 0 * ((0 : ℤ) : R) + X 4 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 20 12 + ((0 : ℤ) : R) * X 0 12) =
      ((3 : ℤ) : R) * X 4 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 4 12
  have i20 : X 4 0 = 0 := hi 20
  have d0_4_13 : X 4 0 * ((3 : ℤ) : R) + X 4 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 20 13 + ((0 : ℤ) : R) * X 0 13) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 4 13
  have d0_4_14 : X 4 0 * ((0 : ℤ) : R) + X 4 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 20 14 + ((0 : ℤ) : R) * X 0 14) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 4 14
  have d0_4_15 : X 4 1 * ((3 : ℤ) : R) + X 4 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 20 15 + ((0 : ℤ) : R) * X 0 15) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 4 15
  have i18 : X 4 1 = 0 := hi 18
  have d0_4_16 : X 4 0 * ((0 : ℤ) : R) + X 4 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 20 16 + ((0 : ℤ) : R) * X 0 16) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 4 16
  have c17 : ((1 : ℤ) : R) * X 4 2 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 17
  have d0_4_17 : X 4 2 * ((3 : ℤ) : R) + X 4 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 20 17 + ((0 : ℤ) : R) * X 0 17) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 4 17
  have d0_4_18 : X 4 0 * ((0 : ℤ) : R) + X 4 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 20 18 + ((0 : ℤ) : R) * X 0 18) =
      ((-3 : ℤ) : R) * X 1 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 4 18
  have i15 : X 1 0 = 0 := hi 15
  have c15 : ((1 : ℤ) : R) * X 4 3 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 15
  have d0_4_19 : X 4 3 * ((3 : ℤ) : R) + X 4 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 20 19 + ((0 : ℤ) : R) * X 0 19) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 4 19
  have c13 : ((1 : ℤ) : R) * X 0 0 + ((1 : ℤ) : R) * X 7 7 = 0 := hc 13
  have d0_4_20 : X 4 4 * ((3 : ℤ) : R) + X 4 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 20 20 + ((0 : ℤ) : R) * X 0 20) =
      ((3 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 4 20
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
  have i13 : X 0 0 = 0 := hi 13
  have d2_9_21 : X 9 0 * ((0 : ℤ) : R) + X 9 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 20 21 + ((0 : ℤ) : R) * X 0 21) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 9 21
  have d0_4_22 : X 4 6 * ((3 : ℤ) : R) + X 4 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 20 22 + ((0 : ℤ) : R) * X 0 22) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 4 22
  have d2_4_18 : X 4 6 * ((-3 : ℤ) : R) + X 4 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 18 + ((0 : ℤ) : R) * X 0 18) =
      ((-3 : ℤ) : R) * X 1 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 4 18
  have i11 : X 1 2 = 0 := hi 11
  have d2_9_23 : X 9 12 * ((2 : ℤ) : R) + X 9 13 * ((-1 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 20 23 + ((0 : ℤ) : R) * X 0 23) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 9 23
  have d3_1_13 : X 1 0 * ((0 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 9 13 + ((0 : ℤ) : R) * X 0 13) =
      ((-3 : ℤ) : R) * X 1 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 1 13
  have i9 : X 1 3 = 0 := hi 9
  have c9 : ((1 : ℤ) : R) * X 1 5 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 9
  have d2_9_24 : X 9 14 * ((3 : ℤ) : R) + X 9 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 20 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 9 24
  have d3_1_14 : X 1 5 * ((3 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 9 14 + ((0 : ℤ) : R) * X 0 14) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 1 14
  have d0_4_25 : X 4 12 * ((-1 : ℤ) : R) + X 4 13 * ((2 : ℤ) : R) -
        (((3 : ℤ) : R) * X 20 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 4 25
  have d5_0_12 : X 0 5 * ((-3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 4 12 + ((0 : ℤ) : R) * X 0 12) =
      ((0 : ℤ) : R) * X 0 5 + ((0 : ℤ) : R) * X 0 5 :=
    hX.entry 5 0 12
  have i4 : X 0 5 = 0 := hi 4
  fin_cases n
  · exact (show X 20 0 = 0 by linear_combination d0_9_2 + ((-1 : R) * X 20 0) * htwo)
  · exact (show X 20 1 = 0 by
      linear_combination c25 + d0_4_1 + ((-2 : R) * X 18 0) * htwo + ((2 : R) * X 20 1) * htwo)
  · exact (show X 20 2 = 0 by linear_combination d0_4_2 + ((2 : R) * X 20 2) * htwo)
  · exact (show X 20 3 = 0 by linear_combination d0_4_3 + ((2 : R) * X 20 3) * htwo)
  · exact (show X 20 4 = 0 by
      linear_combination d0_4_4 + i25 + ((1 : R) * X 12 0) * htwo + ((2 : R) * X 20 4) * htwo)
  · exact (show X 20 5 = 0 by linear_combination d0_4_5 + ((2 : R) * X 20 5) * htwo)
  · exact (show X 20 6 = 0 by
      linear_combination c22 + d0_4_6 + ((-2 : R) * X 11 0) * htwo + ((2 : R) * X 20 6) * htwo)
  · exact (show X 20 7 = 0 by linear_combination d0_4_7 + ((2 : R) * X 20 7) * htwo)
  · exact (show X 20 8 = 0 by
      linear_combination c20 + d0_4_8 + ((1 : R) * X 9 0) * htwo + ((2 : R) * X 20 8) * htwo)
  · exact (show X 20 9 = 0 by
      linear_combination d0_4_9 + i23 + ((1 : R) * X 8 0) * htwo + ((2 : R) * X 20 9) * htwo)
  · exact (show X 20 10 = 0 by linear_combination d0_4_10 + ((2 : R) * X 20 10) * htwo)
  · exact (show X 20 11 = 0 by
      linear_combination d0_4_11 + i22 + ((-2 : R) * X 6 0) * htwo + ((2 : R) * X 20 11) * htwo)
  · exact (show X 20 12 = 0 by
      linear_combination d0_4_12 + i20 + ((1 : R) * X 4 0) * htwo + ((2 : R) * X 20 12) * htwo)
  · exact (show X 20 13 = 0 by
      linear_combination d0_4_13 + i20 + ((-2 : R) * X 4 0) * htwo + ((2 : R) * X 20 13) * htwo)
  · exact (show X 20 14 = 0 by linear_combination d0_4_14 + ((2 : R) * X 20 14) * htwo)
  · exact (show X 20 15 = 0 by
      linear_combination d0_4_15 + i18 + ((-2 : R) * X 4 1) * htwo + ((2 : R) * X 20 15) * htwo)
  · exact (show X 20 16 = 0 by linear_combination d0_4_16 + ((2 : R) * X 20 16) * htwo)
  · exact (show X 20 17 = 0 by
      linear_combination c17 + d0_4_17 + ((-2 : R) * X 4 2) * htwo + ((2 : R) * X 20 17) * htwo)
  · exact (show X 20 18 = 0 by
      linear_combination d0_4_18 + i15 + ((-2 : R) * X 1 0) * htwo + ((2 : R) * X 20 18) * htwo)
  · exact (show X 20 19 = 0 by
      linear_combination c15 + d0_4_19 + ((-2 : R) * X 4 3) * htwo + ((2 : R) * X 20 19) * htwo)
  · exact (show X 20 20 = 0 by
      linear_combination c13 + d0_4_20 + d0_5_21 + d1_0_10 + d1_3_16 + d1_4_18 + d1_7_21 +
        d2_5_16 + d2_6_18 + d3_0_6 + i12 + i13 + ((5 : R) * X 0 0) * htwo +
        ((-3 : R) * X 1 1) * htwo + ((-3 : R) * X 2 2) * htwo + ((-2 : R) * X 7 7) * htwo +
        ((-2 : R) * X 10 10) * htwo + ((-3 : R) * X 16 16) * htwo + ((-3 : R) * X 18 18) * htwo +
        ((2 : R) * X 20 20) * htwo + ((3 : R) * X 21 21) * htwo)
  · exact (show X 20 21 = 0 by linear_combination d2_9_21 + ((-1 : R) * X 20 21) * htwo)
  · exact (show X 20 22 = 0 by
      linear_combination d0_4_22 + d2_4_18 + i11 + ((-2 : R) * X 1 2) * htwo +
        ((2 : R) * X 20 22) * htwo)
  · exact (show X 20 23 = 0 by
      linear_combination d2_9_23 + d3_1_13 + i9 + ((-2 : R) * X 1 3) * htwo +
        ((-1 : R) * X 9 12) * htwo + ((-1 : R) * X 9 13) * htwo + ((-1 : R) * X 20 23) * htwo)
  · exact (show X 20 24 = 0 by
      linear_combination c9 + d2_9_24 + d3_1_14 + ((-2 : R) * X 1 5) * htwo +
        ((-3 : R) * X 9 14) * htwo + ((-1 : R) * X 20 24) * htwo)
  · exact (show X 20 25 = 0 by
      linear_combination d0_4_25 + d5_0_12 + i4 + ((1 : R) * X 0 5) * htwo +
        ((2 : R) * X 4 12) * htwo + ((-1 : R) * X 4 13) * htwo + ((2 : R) * X 20 25) * htwo)

end TauCeti.F4ShortRoot
