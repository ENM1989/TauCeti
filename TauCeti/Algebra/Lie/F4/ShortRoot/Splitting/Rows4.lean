/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.IdealCoordinate

/-!
# Rows 14 to 17 of a derivation with vanishing coordinates

A matrix differentiating the invariant symmetric multiplication of the twenty-six-dimensional
module of type `F₄` modulo two, and annihilated by the twenty-six short-root quotient coordinates
and by the twenty-six ideal coordinates, is zero. This file proves that for the entries in rows
14 to 17.

The derivation equations are graded by the weight of the entry they constrain, so each entry is
determined by the few equations of its own weight together with the vanishing coordinates of that
weight; the proof of each entry is that combination. The equations themselves are the entrywise
form `TauCeti.F4ShortRoot.IsDerivation.entry` of the derivation equations, instantiated at the
relevant indices, and each combination is exact up to multiples of two, which vanish in
characteristic two.

## Main results

* `TauCeti.F4ShortRoot.entry_row_14` and its companions up to
  `TauCeti.F4ShortRoot.entry_row_17`: the entries of these rows vanish.
-/

public section

open Matrix

namespace TauCeti.F4ShortRoot

universe u

variable {R : Type u} [CommRing R] [CharP R 2]

/-- Every entry of the `14`th row of a derivation all of whose coordinates vanish
is zero. -/
theorem entry_row_14 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hq : ∀ p, quotientCoordinate p X = 0) (hi : ∀ a, X (idealRow a) (idealCol a) = 0)
    (n : Fin 26) : X 14 n = 0 := by
  have htwo : (2 : R) = 0 := by exact_mod_cast CharP.cast_eq_zero R 2
  have hc := quotientCoordinate_entries hq
  have c23 : ((1 : ℤ) : R) * X 14 0 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 23
  have d0_14_15 : X 14 1 * ((3 : ℤ) : R) + X 14 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 15 + ((0 : ℤ) : R) * X 0 15) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 14 15
  have d0_14_17 : X 14 2 * ((3 : ℤ) : R) + X 14 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 17 + ((0 : ℤ) : R) * X 0 17) =
      ((-3 : ℤ) : R) * X 10 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 14 17
  have i24 : X 10 0 = 0 := hi 24
  have d0_14_19 : X 14 3 * ((3 : ℤ) : R) + X 14 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 19 + ((0 : ℤ) : R) * X 0 19) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 14 19
  have d0_14_20 : X 14 4 * ((3 : ℤ) : R) + X 14 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 20 + ((0 : ℤ) : R) * X 0 20) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 14 20
  have d0_14_21 : X 14 5 * ((3 : ℤ) : R) + X 14 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 21 + ((0 : ℤ) : R) * X 0 21) =
      ((3 : ℤ) : R) * X 6 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 14 21
  have i22 : X 6 0 = 0 := hi 22
  have d0_14_22 : X 14 6 * ((3 : ℤ) : R) + X 14 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 22 + ((0 : ℤ) : R) * X 0 22) =
      ((-3 : ℤ) : R) * X 5 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 14 22
  have i21 : X 5 0 = 0 := hi 21
  have c19 : ((1 : ℤ) : R) * X 6 1 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 19
  have d1_2_7 : X 2 0 * ((0 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 14 7 + ((0 : ℤ) : R) * X 0 7) =
      ((3 : ℤ) : R) * X 6 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 2 7
  have d0_14_23 : X 14 8 * ((3 : ℤ) : R) + X 14 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 23 + ((0 : ℤ) : R) * X 0 23) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 14 23
  have c16 : ((1 : ℤ) : R) * X 5 1 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 16
  have d1_2_9 : X 2 0 * ((0 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 14 9 + ((0 : ℤ) : R) * X 0 9) =
      ((-3 : ℤ) : R) * X 5 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 2 9
  have d0_14_24 : X 14 10 * ((3 : ℤ) : R) + X 14 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 24 + ((0 : ℤ) : R) * X 0 24) =
      ((3 : ℤ) : R) * X 2 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 14 24
  have i17 : X 2 0 = 0 := hi 17
  have d1_2_11 : X 2 0 * ((0 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 14 11 + ((0 : ℤ) : R) * X 0 11) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 2 11
  have d0_14_25 : X 14 12 * ((-1 : ℤ) : R) + X 14 13 * ((2 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 14 25
  have d1_2_13 : X 2 1 * ((-3 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 14 13 + ((0 : ℤ) : R) * X 0 13) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 2 13
  have i14 : X 2 1 = 0 := hi 14
  have c12 : ((1 : ℤ) : R) * X 0 0 + ((1 : ℤ) : R) * X 11 11 = 0 := hc 12
  have d0_8_23 : X 8 8 * ((3 : ℤ) : R) + X 8 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 23 23 + ((0 : ℤ) : R) * X 0 23) =
      ((3 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 8 23
  have d1_2_14 : X 2 2 * ((-3 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 14 14 + ((0 : ℤ) : R) * X 0 14) =
      ((-3 : ℤ) : R) * X 1 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 2 14
  have d1_11_23 : X 11 11 * ((3 : ℤ) : R) + X 11 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 23 23 + ((0 : ℤ) : R) * X 0 23) =
      ((3 : ℤ) : R) * X 1 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 11 23
  have d2_0_8 : X 0 0 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 8 8 + ((0 : ℤ) : R) * X 0 8) =
      ((3 : ℤ) : R) * X 2 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 0 8
  have i13 : X 0 0 = 0 := hi 13
  have d1_2_15 : X 2 0 * ((0 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 14 15 + ((0 : ℤ) : R) * X 0 15) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 2 15
  have c11 : ((1 : ℤ) : R) * X 2 3 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 11
  have d1_2_16 : X 2 3 * ((-3 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 14 16 + ((0 : ℤ) : R) * X 0 16) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 2 16
  have d1_2_17 : X 2 0 * ((0 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 14 17 + ((0 : ℤ) : R) * X 0 17) =
      ((3 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 2 17
  have i10 : X 0 1 = 0 := hi 10
  have c8 : ((1 : ℤ) : R) * X 2 4 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 8
  have d1_2_18 : X 2 4 * ((-3 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 14 18 + ((0 : ℤ) : R) * X 0 18) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 2 18
  have d1_2_19 : X 2 0 * ((0 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 14 19 + ((0 : ℤ) : R) * X 0 19) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 2 19
  have d1_2_20 : X 2 0 * ((0 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 14 20 + ((0 : ℤ) : R) * X 0 20) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 2 20
  have d0_0_19 : X 0 3 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 13 19 + ((0 : ℤ) : R) * X 0 19) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 0 19
  have d1_1_19 : X 1 0 * ((0 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 12 19 + ((-3 : ℤ) : R) * X 13 19) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 1 19
  have d1_2_21 : X 2 7 * ((3 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 14 21 + ((0 : ℤ) : R) * X 0 21) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 2 21
  have d2_2_19 : X 2 7 * ((-3 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 12 19 + ((0 : ℤ) : R) * X 0 19) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 2 19
  have i6 : X 0 3 = 0 := hi 6
  have d0_0_20 : X 0 4 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 13 20 + ((0 : ℤ) : R) * X 0 20) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 0 20
  have d1_1_20 : X 1 0 * ((0 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 12 20 + ((-3 : ℤ) : R) * X 13 20) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 1 20
  have d1_2_22 : X 2 9 * ((3 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 14 22 + ((0 : ℤ) : R) * X 0 22) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 2 22
  have d2_2_20 : X 2 9 * ((-3 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 12 20 + ((0 : ℤ) : R) * X 0 20) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 2 20
  have i5 : X 0 4 = 0 := hi 5
  have d3_5_23 : X 5 0 * ((0 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 14 23 + ((0 : ℤ) : R) * X 0 23) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 5 23
  have d3_5_24 : X 5 16 * ((3 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 14 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 5 24
  have d4_0_16 : X 0 8 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 5 16 + ((0 : ℤ) : R) * X 0 16) =
      ((0 : ℤ) : R) * X 0 4 + ((0 : ℤ) : R) * X 0 4 :=
    hX.entry 4 0 16
  have i2 : X 0 8 = 0 := hi 2
  have c3 : ((1 : ℤ) : R) * X 0 11 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 3
  have d3_5_25 : X 5 19 * ((3 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 14 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 5 25
  have d4_0_19 : X 0 11 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 5 19 + ((0 : ℤ) : R) * X 0 19) =
      ((0 : ℤ) : R) * X 0 4 + ((0 : ℤ) : R) * X 0 4 :=
    hX.entry 4 0 19
  fin_cases n
  · exact (show X 14 0 = 0 by linear_combination c23)
  · exact (show X 14 1 = 0 by linear_combination d0_14_15 + ((-1 : R) * X 14 1) * htwo)
  · exact (show X 14 2 = 0 by
      linear_combination d0_14_17 + i24 + ((-2 : R) * X 10 0) * htwo +
        ((-1 : R) * X 14 2) * htwo)
  · exact (show X 14 3 = 0 by linear_combination d0_14_19 + ((-1 : R) * X 14 3) * htwo)
  · exact (show X 14 4 = 0 by linear_combination d0_14_20 + ((-1 : R) * X 14 4) * htwo)
  · exact (show X 14 5 = 0 by
      linear_combination d0_14_21 + i22 + ((1 : R) * X 6 0) * htwo + ((-1 : R) * X 14 5) * htwo)
  · exact (show X 14 6 = 0 by
      linear_combination d0_14_22 + i21 + ((-2 : R) * X 5 0) * htwo +
        ((-1 : R) * X 14 6) * htwo)
  · exact (show X 14 7 = 0 by
      linear_combination c19 + d1_2_7 + ((1 : R) * X 6 1) * htwo + ((-1 : R) * X 14 7) * htwo)
  · exact (show X 14 8 = 0 by linear_combination d0_14_23 + ((-1 : R) * X 14 8) * htwo)
  · exact (show X 14 9 = 0 by
      linear_combination c16 + d1_2_9 + ((-2 : R) * X 5 1) * htwo + ((-1 : R) * X 14 9) * htwo)
  · exact (show X 14 10 = 0 by
      linear_combination d0_14_24 + i17 + ((1 : R) * X 2 0) * htwo +
        ((-1 : R) * X 14 10) * htwo)
  · exact (show X 14 11 = 0 by linear_combination d1_2_11 + ((-1 : R) * X 14 11) * htwo)
  · exact (show X 14 12 = 0 by
      linear_combination d0_14_25 + ((1 : R) * X 14 12) * htwo + ((-1 : R) * X 14 13) * htwo)
  · exact (show X 14 13 = 0 by
      linear_combination d1_2_13 + i14 + ((1 : R) * X 2 1) * htwo + ((-1 : R) * X 14 13) * htwo)
  · exact (show X 14 14 = 0 by
      linear_combination c12 + d0_8_23 + d1_2_14 + d1_11_23 + d2_0_8 + i13 +
        ((-1 : R) * X 0 0) * htwo + ((3 : R) * X 2 2) * htwo + ((-2 : R) * X 11 11) * htwo +
        ((-1 : R) * X 14 14) * htwo + ((3 : R) * X 23 23) * htwo)
  · exact (show X 14 15 = 0 by linear_combination d1_2_15 + ((-1 : R) * X 14 15) * htwo)
  · exact (show X 14 16 = 0 by
      linear_combination c11 + d1_2_16 + ((1 : R) * X 2 3) * htwo + ((-1 : R) * X 14 16) * htwo)
  · exact (show X 14 17 = 0 by
      linear_combination d1_2_17 + i10 + ((1 : R) * X 0 1) * htwo + ((-1 : R) * X 14 17) * htwo)
  · exact (show X 14 18 = 0 by
      linear_combination c8 + d1_2_18 + ((1 : R) * X 2 4) * htwo + ((-1 : R) * X 14 18) * htwo)
  · exact (show X 14 19 = 0 by linear_combination d1_2_19 + ((-1 : R) * X 14 19) * htwo)
  · exact (show X 14 20 = 0 by linear_combination d1_2_20 + ((-1 : R) * X 14 20) * htwo)
  · exact (show X 14 21 = 0 by
      linear_combination d0_0_19 + d1_1_19 + d1_2_21 + d2_2_19 + i6 + ((-2 : R) * X 0 3) * htwo +
        ((-1 : R) * X 14 21) * htwo)
  · exact (show X 14 22 = 0 by
      linear_combination d0_0_20 + d1_1_20 + d1_2_22 + d2_2_20 + i5 + ((-2 : R) * X 0 4) * htwo +
        ((-1 : R) * X 14 22) * htwo)
  · exact (show X 14 23 = 0 by linear_combination d3_5_23 + ((2 : R) * X 14 23) * htwo)
  · exact (show X 14 24 = 0 by
      linear_combination d3_5_24 + d4_0_16 + i2 + ((-2 : R) * X 0 8) * htwo +
        ((2 : R) * X 14 24) * htwo)
  · exact (show X 14 25 = 0 by
      linear_combination c3 + d3_5_25 + d4_0_19 + ((-2 : R) * X 0 11) * htwo +
        ((2 : R) * X 14 25) * htwo)

/-- Every entry of the `15`th row of a derivation all of whose coordinates vanish
is zero. -/
theorem entry_row_15 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hq : ∀ p, quotientCoordinate p X = 0) (hi : ∀ a, X (idealRow a) (idealCol a) = 0)
    (n : Fin 26) : X 15 n = 0 := by
  have htwo : (2 : R) = 0 := by exact_mod_cast CharP.cast_eq_zero R 2
  have hc := quotientCoordinate_entries hq
  have d0_7_5 : X 7 0 * ((0 : ℤ) : R) + X 7 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 5 + ((0 : ℤ) : R) * X 0 5) =
      ((-3 : ℤ) : R) * X 15 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 7 5
  have d0_15_15 : X 15 1 * ((3 : ℤ) : R) + X 15 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 15 + ((0 : ℤ) : R) * X 0 15) =
      ((3 : ℤ) : R) * X 12 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 15 15
  have i25 : X 12 0 = 0 := hi 25
  have c22 : ((1 : ℤ) : R) * X 11 0 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 22
  have d0_1_2 : X 1 0 * ((0 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 15 2 + ((0 : ℤ) : R) * X 0 2) =
      ((3 : ℤ) : R) * X 11 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 1 2
  have c20 : ((1 : ℤ) : R) * X 9 0 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 20
  have d0_1_3 : X 1 0 * ((0 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 15 3 + ((0 : ℤ) : R) * X 0 3) =
      ((-3 : ℤ) : R) * X 9 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 1 3
  have c18 : ((1 : ℤ) : R) * X 7 0 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 18
  have d0_1_4 : X 1 0 * ((0 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 15 4 + ((0 : ℤ) : R) * X 0 4) =
      ((3 : ℤ) : R) * X 7 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 1 4
  have d0_1_5 : X 1 0 * ((0 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 15 5 + ((0 : ℤ) : R) * X 0 5) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 1 5
  have d0_1_6 : X 1 0 * ((0 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 15 6 + ((0 : ℤ) : R) * X 0 6) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 1 6
  have d0_1_7 : X 1 0 * ((0 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 15 7 + ((0 : ℤ) : R) * X 0 7) =
      ((3 : ℤ) : R) * X 4 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 1 7
  have i20 : X 4 0 = 0 := hi 20
  have d0_1_8 : X 1 0 * ((0 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 15 8 + ((0 : ℤ) : R) * X 0 8) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 1 8
  have d0_1_9 : X 1 0 * ((0 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 15 9 + ((0 : ℤ) : R) * X 0 9) =
      ((-3 : ℤ) : R) * X 3 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 1 9
  have i19 : X 3 0 = 0 := hi 19
  have d0_1_10 : X 1 0 * ((0 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 15 10 + ((0 : ℤ) : R) * X 0 10) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 1 10
  have d0_1_11 : X 1 0 * ((0 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 15 11 + ((0 : ℤ) : R) * X 0 11) =
      ((3 : ℤ) : R) * X 2 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 1 11
  have i17 : X 2 0 = 0 := hi 17
  have d0_1_12 : X 1 0 * ((0 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 15 12 + ((0 : ℤ) : R) * X 0 12) =
      ((-3 : ℤ) : R) * X 1 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 1 12
  have i15 : X 1 0 = 0 := hi 15
  have d0_1_13 : X 1 0 * ((3 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 15 13 + ((0 : ℤ) : R) * X 0 13) =
      ((-3 : ℤ) : R) * X 1 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 1 13
  have d0_1_14 : X 1 0 * ((0 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 15 14 + ((0 : ℤ) : R) * X 0 14) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 1 14
  have d0_1_15 : X 1 1 * ((3 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 15 15 + ((0 : ℤ) : R) * X 0 15) =
      ((3 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 1 15
  have d1_0_10 : X 0 0 * ((-3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 10 10 + ((0 : ℤ) : R) * X 0 10) =
      ((-3 : ℤ) : R) * X 1 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 0 10
  have i12 : X 10 10 = 0 := hi 12
  have d0_1_16 : X 1 0 * ((0 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 15 16 + ((0 : ℤ) : R) * X 0 16) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 1 16
  have d0_1_17 : X 1 2 * ((3 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 15 17 + ((0 : ℤ) : R) * X 0 17) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 1 17
  have i11 : X 1 2 = 0 := hi 11
  have d0_1_18 : X 1 0 * ((0 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 15 18 + ((0 : ℤ) : R) * X 0 18) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 1 18
  have d0_1_19 : X 1 3 * ((3 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 15 19 + ((0 : ℤ) : R) * X 0 19) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 1 19
  have i9 : X 1 3 = 0 := hi 9
  have d0_1_20 : X 1 4 * ((3 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 15 20 + ((0 : ℤ) : R) * X 0 20) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 1 20
  have i7 : X 1 4 = 0 := hi 7
  have c9 : ((1 : ℤ) : R) * X 1 5 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 9
  have d0_1_21 : X 1 5 * ((3 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 15 21 + ((0 : ℤ) : R) * X 0 21) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 1 21
  have c6 : ((1 : ℤ) : R) * X 1 6 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 6
  have d0_1_22 : X 1 6 * ((3 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 15 22 + ((0 : ℤ) : R) * X 0 22) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 1 22
  have c4 : ((1 : ℤ) : R) * X 1 8 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 4
  have d0_1_23 : X 1 8 * ((3 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 15 23 + ((0 : ℤ) : R) * X 0 23) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 1 23
  have d5_7_24 : X 7 0 * ((0 : ℤ) : R) + X 7 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 15 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 5 + ((0 : ℤ) : R) * X 0 5 :=
    hX.entry 5 7 24
  have d0_1_25 : X 1 12 * ((-1 : ℤ) : R) + X 1 13 * ((2 : ℤ) : R) -
        (((3 : ℤ) : R) * X 15 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 1 25
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
  have d5_1_20 : X 1 12 * ((-1 : ℤ) : R) + X 1 13 * ((-1 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 20 + ((0 : ℤ) : R) * X 0 20) =
      ((0 : ℤ) : R) * X 0 5 + ((0 : ℤ) : R) * X 0 5 :=
    hX.entry 5 1 20
  have d5_2_22 : X 2 14 * ((-3 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 9 22 + ((0 : ℤ) : R) * X 0 22) =
      ((0 : ℤ) : R) * X 0 5 + ((0 : ℤ) : R) * X 0 5 :=
    hX.entry 5 2 22
  have i1 : X 0 10 = 0 := hi 1
  fin_cases n
  · exact (show X 15 0 = 0 by linear_combination d0_7_5 + ((-1 : R) * X 15 0) * htwo)
  · exact (show X 15 1 = 0 by
      linear_combination d0_15_15 + i25 + ((1 : R) * X 12 0) * htwo +
        ((-1 : R) * X 15 1) * htwo)
  · exact (show X 15 2 = 0 by
      linear_combination c22 + d0_1_2 + ((1 : R) * X 11 0) * htwo + ((2 : R) * X 15 2) * htwo)
  · exact (show X 15 3 = 0 by
      linear_combination c20 + d0_1_3 + ((-2 : R) * X 9 0) * htwo + ((2 : R) * X 15 3) * htwo)
  · exact (show X 15 4 = 0 by
      linear_combination c18 + d0_1_4 + ((1 : R) * X 7 0) * htwo + ((2 : R) * X 15 4) * htwo)
  · exact (show X 15 5 = 0 by linear_combination d0_1_5 + ((2 : R) * X 15 5) * htwo)
  · exact (show X 15 6 = 0 by linear_combination d0_1_6 + ((2 : R) * X 15 6) * htwo)
  · exact (show X 15 7 = 0 by
      linear_combination d0_1_7 + i20 + ((1 : R) * X 4 0) * htwo + ((2 : R) * X 15 7) * htwo)
  · exact (show X 15 8 = 0 by linear_combination d0_1_8 + ((2 : R) * X 15 8) * htwo)
  · exact (show X 15 9 = 0 by
      linear_combination d0_1_9 + i19 + ((-2 : R) * X 3 0) * htwo + ((2 : R) * X 15 9) * htwo)
  · exact (show X 15 10 = 0 by linear_combination d0_1_10 + ((2 : R) * X 15 10) * htwo)
  · exact (show X 15 11 = 0 by
      linear_combination d0_1_11 + i17 + ((1 : R) * X 2 0) * htwo + ((2 : R) * X 15 11) * htwo)
  · exact (show X 15 12 = 0 by
      linear_combination d0_1_12 + i15 + ((-2 : R) * X 1 0) * htwo + ((2 : R) * X 15 12) * htwo)
  · exact (show X 15 13 = 0 by
      linear_combination d0_1_13 + ((-3 : R) * X 1 0) * htwo + ((2 : R) * X 15 13) * htwo)
  · exact (show X 15 14 = 0 by linear_combination d0_1_14 + ((2 : R) * X 15 14) * htwo)
  · exact (show X 15 15 = 0 by
      linear_combination d0_1_15 + d1_0_10 + i12 + ((3 : R) * X 0 0) * htwo +
        ((-3 : R) * X 1 1) * htwo + ((-2 : R) * X 10 10) * htwo + ((2 : R) * X 15 15) * htwo)
  · exact (show X 15 16 = 0 by linear_combination d0_1_16 + ((2 : R) * X 15 16) * htwo)
  · exact (show X 15 17 = 0 by
      linear_combination d0_1_17 + i11 + ((-2 : R) * X 1 2) * htwo + ((2 : R) * X 15 17) * htwo)
  · exact (show X 15 18 = 0 by linear_combination d0_1_18 + ((2 : R) * X 15 18) * htwo)
  · exact (show X 15 19 = 0 by
      linear_combination d0_1_19 + i9 + ((-2 : R) * X 1 3) * htwo + ((2 : R) * X 15 19) * htwo)
  · exact (show X 15 20 = 0 by
      linear_combination d0_1_20 + i7 + ((-2 : R) * X 1 4) * htwo + ((2 : R) * X 15 20) * htwo)
  · exact (show X 15 21 = 0 by
      linear_combination c9 + d0_1_21 + ((-2 : R) * X 1 5) * htwo + ((2 : R) * X 15 21) * htwo)
  · exact (show X 15 22 = 0 by
      linear_combination c6 + d0_1_22 + ((-2 : R) * X 1 6) * htwo + ((2 : R) * X 15 22) * htwo)
  · exact (show X 15 23 = 0 by
      linear_combination c4 + d0_1_23 + ((-2 : R) * X 1 8) * htwo + ((2 : R) * X 15 23) * htwo)
  · exact (show X 15 24 = 0 by linear_combination d5_7_24 + ((-1 : R) * X 15 24) * htwo)
  · exact (show X 15 25 = 0 by
      linear_combination d0_1_25 + d2_2_24 + d3_1_22 + d4_4_24 + d5_0_18 + d5_1_20 + d5_2_22 +
        i1 + ((1 : R) * X 0 10) * htwo + ((2 : R) * X 1 12) * htwo + ((-1 : R) * X 1 13) * htwo +
        ((-3 : R) * X 9 22) * htwo + ((3 : R) * X 12 24) * htwo + ((2 : R) * X 15 25) * htwo)

/-- Every entry of the `16`th row of a derivation all of whose coordinates vanish
is zero. -/
theorem entry_row_16 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hq : ∀ p, quotientCoordinate p X = 0) (hi : ∀ a, X (idealRow a) (idealCol a) = 0)
    (n : Fin 26) : X 16 n = 0 := by
  have htwo : (2 : R) = 0 := by exact_mod_cast CharP.cast_eq_zero R 2
  have hc := quotientCoordinate_entries hq
  have c24 : ((1 : ℤ) : R) * X 16 0 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 24
  have d0_16_15 : X 16 1 * ((3 : ℤ) : R) + X 16 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 15 + ((0 : ℤ) : R) * X 0 15) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 16 15
  have d0_16_17 : X 16 2 * ((3 : ℤ) : R) + X 16 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 17 + ((0 : ℤ) : R) * X 0 17) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 16 17
  have d0_16_19 : X 16 3 * ((3 : ℤ) : R) + X 16 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 19 + ((0 : ℤ) : R) * X 0 19) =
      ((-3 : ℤ) : R) * X 10 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 16 19
  have i24 : X 10 0 = 0 := hi 24
  have d0_16_20 : X 16 4 * ((3 : ℤ) : R) + X 16 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 20 + ((0 : ℤ) : R) * X 0 20) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 16 20
  have d0_16_21 : X 16 5 * ((3 : ℤ) : R) + X 16 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 21 + ((0 : ℤ) : R) * X 0 21) =
      ((3 : ℤ) : R) * X 8 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 16 21
  have i23 : X 8 0 = 0 := hi 23
  have d0_16_22 : X 16 6 * ((3 : ℤ) : R) + X 16 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 22 + ((0 : ℤ) : R) * X 0 22) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 16 22
  have c21 : ((1 : ℤ) : R) * X 8 1 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 21
  have d1_3_7 : X 3 0 * ((0 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 16 7 + ((0 : ℤ) : R) * X 0 7) =
      ((3 : ℤ) : R) * X 8 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 3 7
  have d0_16_23 : X 16 8 * ((3 : ℤ) : R) + X 16 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 23 + ((0 : ℤ) : R) * X 0 23) =
      ((-3 : ℤ) : R) * X 5 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 16 23
  have i21 : X 5 0 = 0 := hi 21
  have d1_3_9 : X 3 0 * ((0 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 16 9 + ((0 : ℤ) : R) * X 0 9) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 3 9
  have d0_16_24 : X 16 10 * ((3 : ℤ) : R) + X 16 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 24 + ((0 : ℤ) : R) * X 0 24) =
      ((3 : ℤ) : R) * X 3 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 16 24
  have i19 : X 3 0 = 0 := hi 19
  have c16 : ((1 : ℤ) : R) * X 5 1 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 16
  have d1_3_11 : X 3 0 * ((0 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 16 11 + ((0 : ℤ) : R) * X 0 11) =
      ((-3 : ℤ) : R) * X 5 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 3 11
  have d0_16_25 : X 16 12 * ((-1 : ℤ) : R) + X 16 13 * ((2 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 16 25
  have d1_3_13 : X 3 1 * ((-3 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 16 13 + ((0 : ℤ) : R) * X 0 13) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 3 13
  have i16 : X 3 1 = 0 := hi 16
  have c14 : ((1 : ℤ) : R) * X 3 2 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 14
  have d1_3_14 : X 3 2 * ((-3 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 16 14 + ((0 : ℤ) : R) * X 0 14) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 3 14
  have d1_3_15 : X 3 0 * ((0 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 16 15 + ((0 : ℤ) : R) * X 0 15) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 3 15
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
  have i13 : X 0 0 = 0 := hi 13
  have d1_3_17 : X 3 0 * ((0 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 16 17 + ((0 : ℤ) : R) * X 0 17) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 3 17
  have c10 : ((1 : ℤ) : R) * X 3 4 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 10
  have d1_3_18 : X 3 4 * ((-3 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 16 18 + ((0 : ℤ) : R) * X 0 18) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 3 18
  have d1_3_19 : X 3 0 * ((0 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 16 19 + ((0 : ℤ) : R) * X 0 19) =
      ((3 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 3 19
  have i10 : X 0 1 = 0 := hi 10
  have d1_3_20 : X 3 0 * ((0 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 16 20 + ((0 : ℤ) : R) * X 0 20) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 3 20
  have d1_3_21 : X 3 7 * ((3 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 16 21 + ((0 : ℤ) : R) * X 0 21) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 3 21
  have d2_3_19 : X 3 7 * ((-3 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 19 + ((0 : ℤ) : R) * X 0 19) =
      ((3 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 3 19
  have i8 : X 0 2 = 0 := hi 8
  have d2_5_22 : X 5 0 * ((0 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 16 22 + ((0 : ℤ) : R) * X 0 22) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 5 22
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
  have d3_3_20 : X 3 11 * ((-3 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 12 20 + ((0 : ℤ) : R) * X 0 20) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 3 20
  have i5 : X 0 4 = 0 := hi 5
  have d2_5_24 : X 5 14 * ((3 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 16 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 5 24
  have d4_0_14 : X 0 6 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 5 14 + ((0 : ℤ) : R) * X 0 14) =
      ((0 : ℤ) : R) * X 0 4 + ((0 : ℤ) : R) * X 0 4 :=
    hX.entry 4 0 14
  have i3 : X 0 6 = 0 := hi 3
  have c5 : ((1 : ℤ) : R) * X 0 9 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 5
  have d2_5_25 : X 5 17 * ((3 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 16 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 5 25
  have d4_0_17 : X 0 9 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 5 17 + ((0 : ℤ) : R) * X 0 17) =
      ((0 : ℤ) : R) * X 0 4 + ((0 : ℤ) : R) * X 0 4 :=
    hX.entry 4 0 17
  fin_cases n
  · exact (show X 16 0 = 0 by linear_combination c24)
  · exact (show X 16 1 = 0 by linear_combination d0_16_15 + ((-1 : R) * X 16 1) * htwo)
  · exact (show X 16 2 = 0 by linear_combination d0_16_17 + ((-1 : R) * X 16 2) * htwo)
  · exact (show X 16 3 = 0 by
      linear_combination d0_16_19 + i24 + ((-2 : R) * X 10 0) * htwo +
        ((-1 : R) * X 16 3) * htwo)
  · exact (show X 16 4 = 0 by linear_combination d0_16_20 + ((-1 : R) * X 16 4) * htwo)
  · exact (show X 16 5 = 0 by
      linear_combination d0_16_21 + i23 + ((1 : R) * X 8 0) * htwo + ((-1 : R) * X 16 5) * htwo)
  · exact (show X 16 6 = 0 by linear_combination d0_16_22 + ((-1 : R) * X 16 6) * htwo)
  · exact (show X 16 7 = 0 by
      linear_combination c21 + d1_3_7 + ((1 : R) * X 8 1) * htwo + ((-1 : R) * X 16 7) * htwo)
  · exact (show X 16 8 = 0 by
      linear_combination d0_16_23 + i21 + ((-2 : R) * X 5 0) * htwo +
        ((-1 : R) * X 16 8) * htwo)
  · exact (show X 16 9 = 0 by linear_combination d1_3_9 + ((-1 : R) * X 16 9) * htwo)
  · exact (show X 16 10 = 0 by
      linear_combination d0_16_24 + i19 + ((1 : R) * X 3 0) * htwo +
        ((-1 : R) * X 16 10) * htwo)
  · exact (show X 16 11 = 0 by
      linear_combination c16 + d1_3_11 + ((-2 : R) * X 5 1) * htwo +
        ((-1 : R) * X 16 11) * htwo)
  · exact (show X 16 12 = 0 by
      linear_combination d0_16_25 + ((1 : R) * X 16 12) * htwo + ((-1 : R) * X 16 13) * htwo)
  · exact (show X 16 13 = 0 by
      linear_combination d1_3_13 + i16 + ((1 : R) * X 3 1) * htwo + ((-1 : R) * X 16 13) * htwo)
  · exact (show X 16 14 = 0 by
      linear_combination c14 + d1_3_14 + ((1 : R) * X 3 2) * htwo + ((-1 : R) * X 16 14) * htwo)
  · exact (show X 16 15 = 0 by linear_combination d1_3_15 + ((-1 : R) * X 16 15) * htwo)
  · exact (show X 16 16 = 0 by
      linear_combination c12 + c13 + d0_5_21 + d0_8_23 + d1_7_21 + d1_11_23 + d2_0_8 + d2_5_16 +
        i13 + ((3 : R) * X 1 1) * htwo + ((-2 : R) * X 7 7) * htwo +
        ((-2 : R) * X 11 11) * htwo + ((-1 : R) * X 16 16) * htwo + ((3 : R) * X 21 21) * htwo +
        ((3 : R) * X 23 23) * htwo)
  · exact (show X 16 17 = 0 by linear_combination d1_3_17 + ((-1 : R) * X 16 17) * htwo)
  · exact (show X 16 18 = 0 by
      linear_combination c10 + d1_3_18 + ((1 : R) * X 3 4) * htwo + ((-1 : R) * X 16 18) * htwo)
  · exact (show X 16 19 = 0 by
      linear_combination d1_3_19 + i10 + ((1 : R) * X 0 1) * htwo + ((-1 : R) * X 16 19) * htwo)
  · exact (show X 16 20 = 0 by linear_combination d1_3_20 + ((-1 : R) * X 16 20) * htwo)
  · exact (show X 16 21 = 0 by
      linear_combination d1_3_21 + d2_3_19 + i8 + ((1 : R) * X 0 2) * htwo +
        ((-1 : R) * X 16 21) * htwo)
  · exact (show X 16 22 = 0 by linear_combination d2_5_22 + ((-1 : R) * X 16 22) * htwo)
  · exact (show X 16 23 = 0 by
      linear_combination d0_0_20 + d1_1_20 + d1_3_23 + d3_3_20 + i5 + ((-2 : R) * X 0 4) * htwo +
        ((-1 : R) * X 16 23) * htwo)
  · exact (show X 16 24 = 0 by
      linear_combination d2_5_24 + d4_0_14 + i3 + ((-2 : R) * X 0 6) * htwo +
        ((-1 : R) * X 16 24) * htwo)
  · exact (show X 16 25 = 0 by
      linear_combination c5 + d2_5_25 + d4_0_17 + ((-2 : R) * X 0 9) * htwo +
        ((-1 : R) * X 16 25) * htwo)

/-- Every entry of the `17`th row of a derivation all of whose coordinates vanish
is zero. -/
theorem entry_row_17 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hq : ∀ p, quotientCoordinate p X = 0) (hi : ∀ a, X (idealRow a) (idealCol a) = 0)
    (n : Fin 26) : X 17 n = 0 := by
  have htwo : (2 : R) = 0 := by exact_mod_cast CharP.cast_eq_zero R 2
  have hc := quotientCoordinate_entries hq
  have d0_7_3 : X 7 0 * ((0 : ℤ) : R) + X 7 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3) =
      ((3 : ℤ) : R) * X 17 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 7 3
  have c23 : ((1 : ℤ) : R) * X 14 0 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 23
  have d0_2_1 : X 2 0 * ((0 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 17 1 + ((0 : ℤ) : R) * X 0 1) =
      ((-3 : ℤ) : R) * X 14 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 2 1
  have d0_2_2 : X 2 0 * ((0 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 17 2 + ((0 : ℤ) : R) * X 0 2) =
      ((3 : ℤ) : R) * X 12 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 2 2
  have i25 : X 12 0 = 0 := hi 25
  have d0_2_3 : X 2 0 * ((0 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 17 3 + ((0 : ℤ) : R) * X 0 3) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 2 3
  have d0_2_4 : X 2 0 * ((0 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 17 4 + ((0 : ℤ) : R) * X 0 4) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 2 4
  have c20 : ((1 : ℤ) : R) * X 9 0 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 20
  have d0_2_5 : X 2 0 * ((0 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 17 5 + ((0 : ℤ) : R) * X 0 5) =
      ((-3 : ℤ) : R) * X 9 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 2 5
  have c18 : ((1 : ℤ) : R) * X 7 0 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 18
  have d0_2_6 : X 2 0 * ((0 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 17 6 + ((0 : ℤ) : R) * X 0 6) =
      ((3 : ℤ) : R) * X 7 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 2 6
  have d0_2_7 : X 2 0 * ((0 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 17 7 + ((0 : ℤ) : R) * X 0 7) =
      ((3 : ℤ) : R) * X 6 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 2 7
  have i22 : X 6 0 = 0 := hi 22
  have d0_2_8 : X 2 0 * ((0 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 17 8 + ((0 : ℤ) : R) * X 0 8) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 2 8
  have d0_2_9 : X 2 0 * ((0 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 17 9 + ((0 : ℤ) : R) * X 0 9) =
      ((-3 : ℤ) : R) * X 5 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 2 9
  have i21 : X 5 0 = 0 := hi 21
  have d0_2_10 : X 2 0 * ((0 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 17 10 + ((0 : ℤ) : R) * X 0 10) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 2 10
  have d0_2_11 : X 2 0 * ((0 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 17 11 + ((0 : ℤ) : R) * X 0 11) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 2 11
  have d0_2_12 : X 2 0 * ((0 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 17 12 + ((0 : ℤ) : R) * X 0 12) =
      ((3 : ℤ) : R) * X 2 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 2 12
  have i17 : X 2 0 = 0 := hi 17
  have d0_2_13 : X 2 0 * ((3 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 17 13 + ((0 : ℤ) : R) * X 0 13) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 2 13
  have d0_2_14 : X 2 0 * ((0 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 17 14 + ((0 : ℤ) : R) * X 0 14) =
      ((-3 : ℤ) : R) * X 1 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 2 14
  have i15 : X 1 0 = 0 := hi 15
  have d0_2_15 : X 2 1 * ((3 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 17 15 + ((0 : ℤ) : R) * X 0 15) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 2 15
  have i14 : X 2 1 = 0 := hi 14
  have d0_2_16 : X 2 0 * ((0 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 17 16 + ((0 : ℤ) : R) * X 0 16) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 2 16
  have c12 : ((1 : ℤ) : R) * X 0 0 + ((1 : ℤ) : R) * X 11 11 = 0 := hc 12
  have d0_2_17 : X 2 2 * ((3 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 17 17 + ((0 : ℤ) : R) * X 0 17) =
      ((3 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 2 17
  have d0_8_23 : X 8 8 * ((3 : ℤ) : R) + X 8 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 23 23 + ((0 : ℤ) : R) * X 0 23) =
      ((3 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 8 23
  have d1_0_10 : X 0 0 * ((-3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 10 10 + ((0 : ℤ) : R) * X 0 10) =
      ((-3 : ℤ) : R) * X 1 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 0 10
  have d1_11_23 : X 11 11 * ((3 : ℤ) : R) + X 11 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 23 23 + ((0 : ℤ) : R) * X 0 23) =
      ((3 : ℤ) : R) * X 1 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 11 23
  have d2_0_8 : X 0 0 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 8 8 + ((0 : ℤ) : R) * X 0 8) =
      ((3 : ℤ) : R) * X 2 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 0 8
  have i12 : X 10 10 = 0 := hi 12
  have i13 : X 0 0 = 0 := hi 13
  have d0_2_18 : X 2 0 * ((0 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 17 18 + ((0 : ℤ) : R) * X 0 18) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 2 18
  have c11 : ((1 : ℤ) : R) * X 2 3 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 11
  have d0_2_19 : X 2 3 * ((3 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 17 19 + ((0 : ℤ) : R) * X 0 19) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 2 19
  have c8 : ((1 : ℤ) : R) * X 2 4 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 8
  have d0_2_20 : X 2 4 * ((3 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 17 20 + ((0 : ℤ) : R) * X 0 20) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 2 20
  have d0_2_21 : X 2 5 * ((3 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 17 21 + ((0 : ℤ) : R) * X 0 21) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 2 21
  have d3_2_14 : X 2 5 * ((3 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 14 + ((0 : ℤ) : R) * X 0 14) =
      ((-3 : ℤ) : R) * X 1 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 2 14
  have i9 : X 1 3 = 0 := hi 9
  have d0_2_22 : X 2 6 * ((3 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 17 22 + ((0 : ℤ) : R) * X 0 22) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 2 22
  have d0_3_23 : X 3 8 * ((3 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 19 23 + ((0 : ℤ) : R) * X 0 23) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 3 23
  have d2_2_18 : X 2 6 * ((-3 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 12 18 + ((0 : ℤ) : R) * X 0 18) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 2 18
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
  have d3_7_23 : X 7 0 * ((0 : ℤ) : R) + X 7 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 17 23 + ((0 : ℤ) : R) * X 0 23) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 7 23
  have c4 : ((1 : ℤ) : R) * X 1 8 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 4
  have d3_7_24 : X 7 16 * ((3 : ℤ) : R) + X 7 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 17 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 7 24
  have d4_1_16 : X 1 8 * ((3 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 7 16 + ((0 : ℤ) : R) * X 0 16) =
      ((0 : ℤ) : R) * X 0 4 + ((0 : ℤ) : R) * X 0 4 :=
    hX.entry 4 1 16
  have d0_2_25 : X 2 12 * ((-1 : ℤ) : R) + X 2 13 * ((2 : ℤ) : R) -
        (((3 : ℤ) : R) * X 17 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 2 25
  have d3_0_18 : X 0 8 * ((-3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 6 18 + ((0 : ℤ) : R) * X 0 18) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 0 18
  have d7_2_18 : X 2 12 * ((1 : ℤ) : R) + X 2 13 * ((-2 : ℤ) : R) -
        (((3 : ℤ) : R) * X 6 18 + ((0 : ℤ) : R) * X 0 18) =
      ((0 : ℤ) : R) * X 0 7 + ((0 : ℤ) : R) * X 0 7 :=
    hX.entry 7 2 18
  have i2 : X 0 8 = 0 := hi 2
  fin_cases n
  · exact (show X 17 0 = 0 by linear_combination d0_7_3 + ((2 : R) * X 17 0) * htwo)
  · exact (show X 17 1 = 0 by
      linear_combination c23 + d0_2_1 + ((-2 : R) * X 14 0) * htwo + ((2 : R) * X 17 1) * htwo)
  · exact (show X 17 2 = 0 by
      linear_combination d0_2_2 + i25 + ((1 : R) * X 12 0) * htwo + ((2 : R) * X 17 2) * htwo)
  · exact (show X 17 3 = 0 by linear_combination d0_2_3 + ((2 : R) * X 17 3) * htwo)
  · exact (show X 17 4 = 0 by linear_combination d0_2_4 + ((2 : R) * X 17 4) * htwo)
  · exact (show X 17 5 = 0 by
      linear_combination c20 + d0_2_5 + ((-2 : R) * X 9 0) * htwo + ((2 : R) * X 17 5) * htwo)
  · exact (show X 17 6 = 0 by
      linear_combination c18 + d0_2_6 + ((1 : R) * X 7 0) * htwo + ((2 : R) * X 17 6) * htwo)
  · exact (show X 17 7 = 0 by
      linear_combination d0_2_7 + i22 + ((1 : R) * X 6 0) * htwo + ((2 : R) * X 17 7) * htwo)
  · exact (show X 17 8 = 0 by linear_combination d0_2_8 + ((2 : R) * X 17 8) * htwo)
  · exact (show X 17 9 = 0 by
      linear_combination d0_2_9 + i21 + ((-2 : R) * X 5 0) * htwo + ((2 : R) * X 17 9) * htwo)
  · exact (show X 17 10 = 0 by linear_combination d0_2_10 + ((2 : R) * X 17 10) * htwo)
  · exact (show X 17 11 = 0 by linear_combination d0_2_11 + ((2 : R) * X 17 11) * htwo)
  · exact (show X 17 12 = 0 by
      linear_combination d0_2_12 + i17 + ((1 : R) * X 2 0) * htwo + ((2 : R) * X 17 12) * htwo)
  · exact (show X 17 13 = 0 by
      linear_combination d0_2_13 + i17 + ((-2 : R) * X 2 0) * htwo + ((2 : R) * X 17 13) * htwo)
  · exact (show X 17 14 = 0 by
      linear_combination d0_2_14 + i15 + ((-2 : R) * X 1 0) * htwo + ((2 : R) * X 17 14) * htwo)
  · exact (show X 17 15 = 0 by
      linear_combination d0_2_15 + i14 + ((-2 : R) * X 2 1) * htwo + ((2 : R) * X 17 15) * htwo)
  · exact (show X 17 16 = 0 by linear_combination d0_2_16 + ((2 : R) * X 17 16) * htwo)
  · exact (show X 17 17 = 0 by
      linear_combination c12 + d0_2_17 + d0_8_23 + d1_0_10 + d1_11_23 + d2_0_8 + i12 + i13 +
        ((2 : R) * X 0 0) * htwo + ((-2 : R) * X 10 10) * htwo + ((-2 : R) * X 11 11) * htwo +
        ((2 : R) * X 17 17) * htwo + ((3 : R) * X 23 23) * htwo)
  · exact (show X 17 18 = 0 by linear_combination d0_2_18 + ((2 : R) * X 17 18) * htwo)
  · exact (show X 17 19 = 0 by
      linear_combination c11 + d0_2_19 + ((-2 : R) * X 2 3) * htwo + ((2 : R) * X 17 19) * htwo)
  · exact (show X 17 20 = 0 by
      linear_combination c8 + d0_2_20 + ((-2 : R) * X 2 4) * htwo + ((2 : R) * X 17 20) * htwo)
  · exact (show X 17 21 = 0 by
      linear_combination d0_2_21 + d3_2_14 + i9 + ((-2 : R) * X 1 3) * htwo +
        ((-3 : R) * X 2 5) * htwo + ((2 : R) * X 17 21) * htwo)
  · exact (show X 17 22 = 0 by
      linear_combination d0_2_22 + d0_3_23 + d2_2_18 + d2_7_23 + d3_3_18 + d4_1_13 + i7 +
        ((-2 : R) * X 1 4) * htwo + ((-1 : R) * X 7 12) * htwo + ((2 : R) * X 7 13) * htwo +
        ((3 : R) * X 12 18) * htwo + ((2 : R) * X 17 22) * htwo)
  · exact (show X 17 23 = 0 by linear_combination d3_7_23 + ((2 : R) * X 17 23) * htwo)
  · exact (show X 17 24 = 0 by
      linear_combination c4 + d3_7_24 + d4_1_16 + ((-2 : R) * X 1 8) * htwo +
        ((2 : R) * X 17 24) * htwo)
  · exact (show X 17 25 = 0 by
      linear_combination d0_2_25 + d3_0_18 + d7_2_18 + i2 + ((1 : R) * X 0 8) * htwo +
        ((2 : R) * X 17 25) * htwo)

end TauCeti.F4ShortRoot
