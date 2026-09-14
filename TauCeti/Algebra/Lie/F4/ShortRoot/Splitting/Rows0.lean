/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.IdealCoordinate

/-!
# Rows 0 to 3 of a derivation with vanishing coordinates

A matrix differentiating the invariant symmetric multiplication of the twenty-six-dimensional
module of type `F₄` modulo two, and annihilated by the twenty-six short-root quotient coordinates
and by the twenty-six ideal coordinates, is zero. This file proves that for the entries in rows
0 to 3.

The derivation equations are graded by the weight of the entry they constrain, so each entry is
determined by the few equations of its own weight together with the vanishing coordinates of that
weight; the proof of each entry is that combination. The equations themselves are the entrywise
form `TauCeti.F4ShortRoot.IsDerivation.entry` of the derivation equations, instantiated at the
relevant indices, and each combination is exact up to multiples of two, which vanish in
characteristic two.

## Main results

* `TauCeti.F4ShortRoot.entry_row_0` and its companions up to
  `TauCeti.F4ShortRoot.entry_row_3`: the entries of these rows vanish.
-/

public section

open Matrix

namespace TauCeti.F4ShortRoot

universe u

variable {R : Type u} [CommRing R] [CharP R 2]

/-- Every entry of the `0`th row of a derivation all of whose coordinates vanish
is zero. -/
theorem entry_row_0 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hq : ∀ p, quotientCoordinate p X = 0) (hi : ∀ a, X (idealRow a) (idealCol a) = 0)
    (n : Fin 26) : X 0 n = 0 := by
  have htwo : (2 : R) = 0 := by exact_mod_cast CharP.cast_eq_zero R 2
  have hc := quotientCoordinate_entries hq
  have i13 : X 0 0 = 0 := hi 13
  have i10 : X 0 1 = 0 := hi 10
  have i8 : X 0 2 = 0 := hi 8
  have i6 : X 0 3 = 0 := hi 6
  have i5 : X 0 4 = 0 := hi 5
  have i4 : X 0 5 = 0 := hi 4
  have i3 : X 0 6 = 0 := hi 3
  have c7 : ((1 : ℤ) : R) * X 0 7 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 7
  have i2 : X 0 8 = 0 := hi 2
  have c5 : ((1 : ℤ) : R) * X 0 9 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 5
  have i1 : X 0 10 = 0 := hi 1
  have c3 : ((1 : ℤ) : R) * X 0 11 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 3
  have d7_0_18 : X 0 12 * ((1 : ℤ) : R) + X 0 13 * ((-2 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 18 + ((0 : ℤ) : R) * X 0 18) =
      ((0 : ℤ) : R) * X 0 7 + ((0 : ℤ) : R) * X 0 7 :=
    hX.entry 7 0 18
  have i0 : X 0 13 = 0 := hi 0
  have c2 : ((1 : ℤ) : R) * X 0 14 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 2
  have d7_0_20 : X 0 15 * ((-3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 20 + ((0 : ℤ) : R) * X 0 20) =
      ((0 : ℤ) : R) * X 0 7 + ((0 : ℤ) : R) * X 0 7 :=
    hX.entry 7 0 20
  have c1 : ((1 : ℤ) : R) * X 0 16 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 1
  have d7_0_22 : X 0 17 * ((-3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 22 + ((0 : ℤ) : R) * X 0 22) =
      ((0 : ℤ) : R) * X 0 7 + ((0 : ℤ) : R) * X 0 7 :=
    hX.entry 7 0 22
  have c0 : ((1 : ℤ) : R) * X 0 18 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 0
  have d7_0_23 : X 0 19 * ((-3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 23 + ((0 : ℤ) : R) * X 0 23) =
      ((0 : ℤ) : R) * X 0 7 + ((0 : ℤ) : R) * X 0 7 :=
    hX.entry 7 0 23
  have d9_0_23 : X 0 20 * ((-3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 23 + ((0 : ℤ) : R) * X 0 23) =
      ((0 : ℤ) : R) * X 0 9 + ((0 : ℤ) : R) * X 0 9 :=
    hX.entry 9 0 23
  have d7_0_24 : X 0 21 * ((-3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 7 + ((0 : ℤ) : R) * X 0 7 :=
    hX.entry 7 0 24
  have d9_0_24 : X 0 22 * ((-3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 9 + ((0 : ℤ) : R) * X 0 9 :=
    hX.entry 9 0 24
  have d11_0_24 : X 0 23 * ((-3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 11 + ((0 : ℤ) : R) * X 0 11 :=
    hX.entry 11 0 24
  have d12_0_24 : X 0 24 * ((-3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 12 + ((0 : ℤ) : R) * X 0 12 :=
    hX.entry 12 0 24
  have d15_0_24 : X 0 25 * ((-3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 15 + ((0 : ℤ) : R) * X 0 15 :=
    hX.entry 15 0 24
  fin_cases n
  · exact (show X 0 0 = 0 by linear_combination i13)
  · exact (show X 0 1 = 0 by linear_combination i10)
  · exact (show X 0 2 = 0 by linear_combination i8)
  · exact (show X 0 3 = 0 by linear_combination i6)
  · exact (show X 0 4 = 0 by linear_combination i5)
  · exact (show X 0 5 = 0 by linear_combination i4)
  · exact (show X 0 6 = 0 by linear_combination i3)
  · exact (show X 0 7 = 0 by linear_combination c7)
  · exact (show X 0 8 = 0 by linear_combination i2)
  · exact (show X 0 9 = 0 by linear_combination c5)
  · exact (show X 0 10 = 0 by linear_combination i1)
  · exact (show X 0 11 = 0 by linear_combination c3)
  · exact (show X 0 12 = 0 by linear_combination d7_0_18 + ((1 : R) * X 0 13) * htwo)
  · exact (show X 0 13 = 0 by linear_combination i0)
  · exact (show X 0 14 = 0 by linear_combination c2)
  · exact (show X 0 15 = 0 by linear_combination d7_0_20 + ((2 : R) * X 0 15) * htwo)
  · exact (show X 0 16 = 0 by linear_combination c1)
  · exact (show X 0 17 = 0 by linear_combination d7_0_22 + ((2 : R) * X 0 17) * htwo)
  · exact (show X 0 18 = 0 by linear_combination c0)
  · exact (show X 0 19 = 0 by linear_combination d7_0_23 + ((2 : R) * X 0 19) * htwo)
  · exact (show X 0 20 = 0 by linear_combination d9_0_23 + ((2 : R) * X 0 20) * htwo)
  · exact (show X 0 21 = 0 by linear_combination d7_0_24 + ((2 : R) * X 0 21) * htwo)
  · exact (show X 0 22 = 0 by linear_combination d9_0_24 + ((2 : R) * X 0 22) * htwo)
  · exact (show X 0 23 = 0 by linear_combination d11_0_24 + ((2 : R) * X 0 23) * htwo)
  · exact (show X 0 24 = 0 by linear_combination d12_0_24 + ((2 : R) * X 0 24) * htwo)
  · exact (show X 0 25 = 0 by linear_combination d15_0_24 + ((2 : R) * X 0 25) * htwo)

/-- Every entry of the `1`th row of a derivation all of whose coordinates vanish
is zero. -/
theorem entry_row_1 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hq : ∀ p, quotientCoordinate p X = 0) (hi : ∀ a, X (idealRow a) (idealCol a) = 0)
    (n : Fin 26) : X 1 n = 0 := by
  have htwo : (2 : R) = 0 := by exact_mod_cast CharP.cast_eq_zero R 2
  have hc := quotientCoordinate_entries hq
  have i15 : X 1 0 = 0 := hi 15
  have d1_0_10 : X 0 0 * ((-3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 10 10 + ((0 : ℤ) : R) * X 0 10) =
      ((-3 : ℤ) : R) * X 1 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 0 10
  have i12 : X 10 10 = 0 := hi 12
  have i13 : X 0 0 = 0 := hi 13
  have i11 : X 1 2 = 0 := hi 11
  have i9 : X 1 3 = 0 := hi 9
  have i7 : X 1 4 = 0 := hi 7
  have c9 : ((1 : ℤ) : R) * X 1 5 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 9
  have c6 : ((1 : ℤ) : R) * X 1 6 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 6
  have d0_4_25 : X 4 12 * ((-1 : ℤ) : R) + X 4 13 * ((2 : ℤ) : R) -
        (((3 : ℤ) : R) * X 20 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 4 25
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
  have c4 : ((1 : ℤ) : R) * X 1 8 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 4
  have d0_3_25 : X 3 12 * ((-1 : ℤ) : R) + X 3 13 * ((2 : ℤ) : R) -
        (((3 : ℤ) : R) * X 19 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 3 25
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
  have d5_1_18 : X 1 10 * ((-3 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 18 + ((0 : ℤ) : R) * X 0 18) =
      ((0 : ℤ) : R) * X 0 5 + ((0 : ℤ) : R) * X 0 5 :=
    hX.entry 5 1 18
  have d0_2_25 : X 2 12 * ((-1 : ℤ) : R) + X 2 13 * ((2 : ℤ) : R) -
        (((3 : ℤ) : R) * X 17 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 2 25
  have d3_0_18 : X 0 8 * ((-3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 6 18 + ((0 : ℤ) : R) * X 0 18) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 0 18
  have d3_7_25 : X 7 19 * ((3 : ℤ) : R) + X 7 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 17 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 7 25
  have d4_1_19 : X 1 11 * ((3 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 7 19 + ((0 : ℤ) : R) * X 0 19) =
      ((0 : ℤ) : R) * X 0 4 + ((0 : ℤ) : R) * X 0 4 :=
    hX.entry 4 1 19
  have d7_2_18 : X 2 12 * ((1 : ℤ) : R) + X 2 13 * ((-2 : ℤ) : R) -
        (((3 : ℤ) : R) * X 6 18 + ((0 : ℤ) : R) * X 0 18) =
      ((0 : ℤ) : R) * X 0 7 + ((0 : ℤ) : R) * X 0 7 :=
    hX.entry 7 2 18
  have i2 : X 0 8 = 0 := hi 2
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
  have d5_1_22 : X 1 14 * ((-3 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 22 + ((0 : ℤ) : R) * X 0 22) =
      ((0 : ℤ) : R) * X 0 5 + ((0 : ℤ) : R) * X 0 5 :=
    hX.entry 5 1 22
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
  have d7_1_20 : X 1 15 * ((-3 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 4 20 + ((0 : ℤ) : R) * X 0 20) =
      ((0 : ℤ) : R) * X 0 7 + ((0 : ℤ) : R) * X 0 7 :=
    hX.entry 7 1 20
  have d7_2_22 : X 2 17 * ((-3 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 6 22 + ((0 : ℤ) : R) * X 0 22) =
      ((0 : ℤ) : R) * X 0 7 + ((0 : ℤ) : R) * X 0 7 :=
    hX.entry 7 2 22
  have i0 : X 0 13 = 0 := hi 0
  have d5_1_23 : X 1 16 * ((-3 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 23 + ((0 : ℤ) : R) * X 0 23) =
      ((0 : ℤ) : R) * X 0 5 + ((0 : ℤ) : R) * X 0 5 :=
    hX.entry 5 1 23
  have c2 : ((1 : ℤ) : R) * X 0 14 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 2
  have d2_1_25 : X 1 17 * ((3 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 11 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 1 25
  have d5_3_25 : X 3 21 * ((3 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 11 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 5 + ((0 : ℤ) : R) * X 0 5 :=
    hX.entry 5 3 25
  have d6_0_21 : X 0 14 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 3 21 + ((0 : ℤ) : R) * X 0 21) =
      ((0 : ℤ) : R) * X 0 6 + ((0 : ℤ) : R) * X 0 6 :=
    hX.entry 6 0 21
  have d6_1_23 : X 1 18 * ((-3 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 23 + ((0 : ℤ) : R) * X 0 23) =
      ((0 : ℤ) : R) * X 0 6 + ((0 : ℤ) : R) * X 0 6 :=
    hX.entry 6 1 23
  have c1 : ((1 : ℤ) : R) * X 0 16 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 1
  have d5_0_23 : X 0 16 * ((-3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 4 23 + ((0 : ℤ) : R) * X 0 23) =
      ((0 : ℤ) : R) * X 0 5 + ((0 : ℤ) : R) * X 0 5 :=
    hX.entry 5 0 23
  have d7_1_23 : X 1 19 * ((-3 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 4 23 + ((0 : ℤ) : R) * X 0 23) =
      ((0 : ℤ) : R) * X 0 7 + ((0 : ℤ) : R) * X 0 7 :=
    hX.entry 7 1 23
  have c0 : ((1 : ℤ) : R) * X 0 18 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 0
  have d4_1_25 : X 1 20 * ((3 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 7 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 4 + ((0 : ℤ) : R) * X 0 4 :=
    hX.entry 4 1 25
  have d6_2_25 : X 2 22 * ((3 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 7 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 6 + ((0 : ℤ) : R) * X 0 6 :=
    hX.entry 6 2 25
  have d8_0_22 : X 0 18 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 2 22 + ((0 : ℤ) : R) * X 0 22) =
      ((0 : ℤ) : R) * X 0 8 + ((0 : ℤ) : R) * X 0 8 :=
    hX.entry 8 0 22
  have d5_1_25 : X 1 21 * ((3 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 5 + ((0 : ℤ) : R) * X 0 5 :=
    hX.entry 5 1 25
  have d6_1_25 : X 1 22 * ((3 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 6 + ((0 : ℤ) : R) * X 0 6 :=
    hX.entry 6 1 25
  have d8_1_25 : X 1 23 * ((3 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 8 + ((0 : ℤ) : R) * X 0 8 :=
    hX.entry 8 1 25
  have d10_0_24 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 1 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 10 + ((0 : ℤ) : R) * X 0 10 :=
    hX.entry 10 0 24
  have d12_1_25 : X 1 0 * ((0 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 1 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 12 + ((0 : ℤ) : R) * X 0 12 :=
    hX.entry 12 1 25
  fin_cases n
  · exact (show X 1 0 = 0 by linear_combination i15)
  · exact (show X 1 1 = 0 by
      linear_combination d1_0_10 + i12 + i13 + ((1 : R) * X 0 0) * htwo +
        ((-1 : R) * X 1 1) * htwo + ((-2 : R) * X 10 10) * htwo)
  · exact (show X 1 2 = 0 by linear_combination i11)
  · exact (show X 1 3 = 0 by linear_combination i9)
  · exact (show X 1 4 = 0 by linear_combination i7)
  · exact (show X 1 5 = 0 by linear_combination c9)
  · exact (show X 1 6 = 0 by linear_combination c6)
  · exact (show X 1 7 = 0 by
      linear_combination d0_4_25 + d2_9_25 + d3_1_17 + d5_0_12 + i4 + ((1 : R) * X 0 5) * htwo +
        ((-1 : R) * X 1 7) * htwo + ((2 : R) * X 4 12) * htwo + ((-1 : R) * X 4 13) * htwo +
        ((-3 : R) * X 9 17) * htwo)
  · exact (show X 1 8 = 0 by linear_combination c4)
  · exact (show X 1 9 = 0 by
      linear_combination d0_3_25 + d2_7_25 + d4_1_17 + d6_0_12 + i3 + ((1 : R) * X 0 6) * htwo +
        ((-1 : R) * X 1 9) * htwo + ((-1 : R) * X 3 12) * htwo + ((-1 : R) * X 3 13) * htwo)
  · exact (show X 1 10 = 0 by linear_combination d5_1_18 + ((2 : R) * X 1 10) * htwo)
  · exact (show X 1 11 = 0 by
      linear_combination d0_2_25 + d3_0_18 + d3_7_25 + d4_1_19 + d7_2_18 + i2 +
        ((1 : R) * X 0 8) * htwo + ((-1 : R) * X 1 11) * htwo + ((3 : R) * X 17 25) * htwo)
  · exact (show X 1 12 = 0 by
      linear_combination d2_2_24 + d3_1_22 + d4_4_24 + d5_0_18 + d5_1_20 + d5_2_22 + i1 +
        ((1 : R) * X 0 10) * htwo + ((2 : R) * X 1 12) * htwo + ((-3 : R) * X 9 22) * htwo +
        ((3 : R) * X 12 24) * htwo)
  · exact (show X 1 13 = 0 by
      linear_combination d2_2_24 + d3_1_22 + d4_4_24 + d5_0_18 + d5_2_22 + i1 +
        ((1 : R) * X 0 10) * htwo + ((1 : R) * X 1 12) * htwo + ((-3 : R) * X 9 22) * htwo +
        ((3 : R) * X 12 24) * htwo)
  · exact (show X 1 14 = 0 by linear_combination d5_1_22 + ((2 : R) * X 1 14) * htwo)
  · exact (show X 1 15 = 0 by
      linear_combination d2_2_25 + d3_0_22 + d4_4_25 + d7_1_20 + d7_2_22 + i0 +
        ((1 : R) * X 0 12) * htwo + ((-1 : R) * X 0 13) * htwo + ((2 : R) * X 1 15) * htwo +
        ((3 : R) * X 12 25) * htwo)
  · exact (show X 1 16 = 0 by linear_combination d5_1_23 + ((2 : R) * X 1 16) * htwo)
  · exact (show X 1 17 = 0 by
      linear_combination c2 + d2_1_25 + d5_3_25 + d6_0_21 + ((-2 : R) * X 0 14) * htwo +
        ((-1 : R) * X 1 17) * htwo + ((-3 : R) * X 3 21) * htwo)
  · exact (show X 1 18 = 0 by linear_combination d6_1_23 + ((2 : R) * X 1 18) * htwo)
  · exact (show X 1 19 = 0 by
      linear_combination c1 + d5_0_23 + d7_1_23 + ((1 : R) * X 0 16) * htwo +
        ((2 : R) * X 1 19) * htwo + ((3 : R) * X 4 23) * htwo)
  · exact (show X 1 20 = 0 by
      linear_combination c0 + d4_1_25 + d6_2_25 + d8_0_22 + ((-2 : R) * X 0 18) * htwo +
        ((-1 : R) * X 1 20) * htwo + ((3 : R) * X 7 25) * htwo)
  · exact (show X 1 21 = 0 by linear_combination d5_1_25 + ((-1 : R) * X 1 21) * htwo)
  · exact (show X 1 22 = 0 by linear_combination d6_1_25 + ((-1 : R) * X 1 22) * htwo)
  · exact (show X 1 23 = 0 by linear_combination d8_1_25 + ((-1 : R) * X 1 23) * htwo)
  · exact (show X 1 24 = 0 by linear_combination d10_0_24 + ((-1 : R) * X 1 24) * htwo)
  · exact (show X 1 25 = 0 by linear_combination d12_1_25 + ((-1 : R) * X 1 25) * htwo)

/-- Every entry of the `2`th row of a derivation all of whose coordinates vanish
is zero. -/
theorem entry_row_2 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hq : ∀ p, quotientCoordinate p X = 0) (hi : ∀ a, X (idealRow a) (idealCol a) = 0)
    (n : Fin 26) : X 2 n = 0 := by
  have htwo : (2 : R) = 0 := by exact_mod_cast CharP.cast_eq_zero R 2
  have hc := quotientCoordinate_entries hq
  have i17 : X 2 0 = 0 := hi 17
  have i14 : X 2 1 = 0 := hi 14
  have c12 : ((1 : ℤ) : R) * X 0 0 + ((1 : ℤ) : R) * X 11 11 = 0 := hc 12
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
  have c11 : ((1 : ℤ) : R) * X 2 3 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 11
  have c8 : ((1 : ℤ) : R) * X 2 4 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 8
  have d3_2_14 : X 2 5 * ((3 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 14 + ((0 : ℤ) : R) * X 0 14) =
      ((-3 : ℤ) : R) * X 1 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 2 14
  have i9 : X 1 3 = 0 := hi 9
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
  have d0_0_19 : X 0 3 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 13 19 + ((0 : ℤ) : R) * X 0 19) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 0 19
  have d1_1_19 : X 1 0 * ((0 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 12 19 + ((-3 : ℤ) : R) * X 13 19) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 1 19
  have d2_2_19 : X 2 7 * ((-3 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 12 19 + ((0 : ℤ) : R) * X 0 19) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 2 19
  have i6 : X 0 3 = 0 := hi 6
  have d3_2_18 : X 2 8 * ((-3 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 18 + ((0 : ℤ) : R) * X 0 18) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 2 18
  have d0_0_20 : X 0 4 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 13 20 + ((0 : ℤ) : R) * X 0 20) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 0 20
  have d1_1_20 : X 1 0 * ((0 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 12 20 + ((-3 : ℤ) : R) * X 13 20) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 1 20
  have d2_2_20 : X 2 9 * ((-3 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 12 20 + ((0 : ℤ) : R) * X 0 20) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 2 20
  have i5 : X 0 4 = 0 := hi 5
  have c4 : ((1 : ℤ) : R) * X 1 8 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 4
  have d0_2_24 : X 2 10 * ((3 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 17 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 2 24
  have d3_7_24 : X 7 16 * ((3 : ℤ) : R) + X 7 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 17 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 7 24
  have d4_1_16 : X 1 8 * ((3 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 7 16 + ((0 : ℤ) : R) * X 0 16) =
      ((0 : ℤ) : R) * X 0 4 + ((0 : ℤ) : R) * X 0 4 :=
    hX.entry 4 1 16
  have d3_2_20 : X 2 11 * ((-3 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 20 + ((0 : ℤ) : R) * X 0 20) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 2 20
  have d3_0_18 : X 0 8 * ((-3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 6 18 + ((0 : ℤ) : R) * X 0 18) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 0 18
  have d7_2_18 : X 2 12 * ((1 : ℤ) : R) + X 2 13 * ((-2 : ℤ) : R) -
        (((3 : ℤ) : R) * X 6 18 + ((0 : ℤ) : R) * X 0 18) =
      ((0 : ℤ) : R) * X 0 7 + ((0 : ℤ) : R) * X 0 7 :=
    hX.entry 7 2 18
  have i2 : X 0 8 = 0 := hi 2
  have d3_2_22 : X 2 12 * ((-2 : ℤ) : R) + X 2 13 * ((1 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 22 + ((0 : ℤ) : R) * X 0 22) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 2 22
  have d2_2_24 : X 2 14 * ((3 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 12 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 2 24
  have d4_4_24 : X 4 18 * ((3 : ℤ) : R) + X 4 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 12 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 4 + ((0 : ℤ) : R) * X 0 4 :=
    hX.entry 4 4 24
  have d5_0_18 : X 0 10 * ((-3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 4 18 + ((0 : ℤ) : R) * X 0 18) =
      ((0 : ℤ) : R) * X 0 5 + ((0 : ℤ) : R) * X 0 5 :=
    hX.entry 5 0 18
  have i1 : X 0 10 = 0 := hi 1
  have c3 : ((1 : ℤ) : R) * X 0 11 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 3
  have d1_2_25 : X 2 15 * ((3 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 14 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 2 25
  have d3_5_25 : X 5 19 * ((3 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 14 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 5 25
  have d4_0_19 : X 0 11 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 5 19 + ((0 : ℤ) : R) * X 0 19) =
      ((0 : ℤ) : R) * X 0 4 + ((0 : ℤ) : R) * X 0 4 :=
    hX.entry 4 0 19
  have d3_2_24 : X 2 16 * ((3 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 2 24
  have d3_0_22 : X 0 12 * ((-2 : ℤ) : R) + X 0 13 * ((1 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 6 22 + ((0 : ℤ) : R) * X 0 22) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 0 22
  have d7_2_22 : X 2 17 * ((-3 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 6 22 + ((0 : ℤ) : R) * X 0 22) =
      ((0 : ℤ) : R) * X 0 7 + ((0 : ℤ) : R) * X 0 7 :=
    hX.entry 7 2 22
  have i0 : X 0 13 = 0 := hi 0
  have d4_2_24 : X 2 18 * ((3 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 4 + ((0 : ℤ) : R) * X 0 4 :=
    hX.entry 4 2 24
  have d3_2_25 : X 2 19 * ((3 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 2 25
  have d4_2_25 : X 2 20 * ((3 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 4 + ((0 : ℤ) : R) * X 0 4 :=
    hX.entry 4 2 25
  have c1 : ((1 : ℤ) : R) * X 0 16 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 1
  have d3_1_25 : X 1 19 * ((3 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 9 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 1 25
  have d5_0_23 : X 0 16 * ((-3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 4 23 + ((0 : ℤ) : R) * X 0 23) =
      ((0 : ℤ) : R) * X 0 5 + ((0 : ℤ) : R) * X 0 5 :=
    hX.entry 5 0 23
  have d5_2_25 : X 2 21 * ((3 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 9 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 5 + ((0 : ℤ) : R) * X 0 5 :=
    hX.entry 5 2 25
  have d7_1_23 : X 1 19 * ((-3 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 4 23 + ((0 : ℤ) : R) * X 0 23) =
      ((0 : ℤ) : R) * X 0 7 + ((0 : ℤ) : R) * X 0 7 :=
    hX.entry 7 1 23
  have c0 : ((1 : ℤ) : R) * X 0 18 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 0
  have d8_0_22 : X 0 18 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 2 22 + ((0 : ℤ) : R) * X 0 22) =
      ((0 : ℤ) : R) * X 0 8 + ((0 : ℤ) : R) * X 0 8 :=
    hX.entry 8 0 22
  have d8_0_23 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 2 23 + ((0 : ℤ) : R) * X 0 23) =
      ((0 : ℤ) : R) * X 0 8 + ((0 : ℤ) : R) * X 0 8 :=
    hX.entry 8 0 23
  have d8_0_24 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 2 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 8 + ((0 : ℤ) : R) * X 0 8 :=
    hX.entry 8 0 24
  have d11_1_25 : X 1 0 * ((0 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 2 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 11 + ((0 : ℤ) : R) * X 0 11 :=
    hX.entry 11 1 25
  fin_cases n
  · exact (show X 2 0 = 0 by linear_combination i17)
  · exact (show X 2 1 = 0 by linear_combination i14)
  · exact (show X 2 2 = 0 by
      linear_combination c12 + d0_8_23 + d1_0_10 + d1_11_23 + d2_0_8 + i12 +
        ((1 : R) * X 0 0) * htwo + ((2 : R) * X 2 2) * htwo + ((-2 : R) * X 10 10) * htwo +
        ((-2 : R) * X 11 11) * htwo + ((3 : R) * X 23 23) * htwo)
  · exact (show X 2 3 = 0 by linear_combination c11)
  · exact (show X 2 4 = 0 by linear_combination c8)
  · exact (show X 2 5 = 0 by
      linear_combination d3_2_14 + i9 + ((-2 : R) * X 1 3) * htwo + ((-1 : R) * X 2 5) * htwo)
  · exact (show X 2 6 = 0 by
      linear_combination d0_3_23 + d2_2_18 + d2_7_23 + d3_3_18 + d4_1_13 + i7 +
        ((-2 : R) * X 1 4) * htwo + ((2 : R) * X 2 6) * htwo + ((-1 : R) * X 7 12) * htwo +
        ((2 : R) * X 7 13) * htwo + ((3 : R) * X 12 18) * htwo)
  · exact (show X 2 7 = 0 by
      linear_combination d0_0_19 + d1_1_19 + d2_2_19 + i6 + ((-2 : R) * X 0 3) * htwo +
        ((2 : R) * X 2 7) * htwo)
  · exact (show X 2 8 = 0 by linear_combination d3_2_18 + ((2 : R) * X 2 8) * htwo)
  · exact (show X 2 9 = 0 by
      linear_combination d0_0_20 + d1_1_20 + d2_2_20 + i5 + ((-2 : R) * X 0 4) * htwo +
        ((2 : R) * X 2 9) * htwo)
  · exact (show X 2 10 = 0 by
      linear_combination c4 + d0_2_24 + d3_7_24 + d4_1_16 + ((-2 : R) * X 1 8) * htwo +
        ((-1 : R) * X 2 10) * htwo + ((3 : R) * X 17 24) * htwo)
  · exact (show X 2 11 = 0 by linear_combination d3_2_20 + ((2 : R) * X 2 11) * htwo)
  · exact (show X 2 12 = 0 by
      linear_combination d3_0_18 + d7_2_18 + i2 + ((1 : R) * X 0 8) * htwo +
        ((1 : R) * X 2 13) * htwo)
  · exact (show X 2 13 = 0 by linear_combination d3_2_22 + ((1 : R) * X 2 12) * htwo)
  · exact (show X 2 14 = 0 by
      linear_combination d2_2_24 + d4_4_24 + d5_0_18 + i1 + ((1 : R) * X 0 10) * htwo +
        ((-1 : R) * X 2 14) * htwo + ((3 : R) * X 12 24) * htwo)
  · exact (show X 2 15 = 0 by
      linear_combination c3 + d1_2_25 + d3_5_25 + d4_0_19 + ((-2 : R) * X 0 11) * htwo +
        ((-1 : R) * X 2 15) * htwo)
  · exact (show X 2 16 = 0 by linear_combination d3_2_24 + ((-1 : R) * X 2 16) * htwo)
  · exact (show X 2 17 = 0 by
      linear_combination d3_0_22 + d7_2_22 + i0 + ((1 : R) * X 0 12) * htwo +
        ((-1 : R) * X 0 13) * htwo + ((2 : R) * X 2 17) * htwo)
  · exact (show X 2 18 = 0 by linear_combination d4_2_24 + ((-1 : R) * X 2 18) * htwo)
  · exact (show X 2 19 = 0 by linear_combination d3_2_25 + ((-1 : R) * X 2 19) * htwo)
  · exact (show X 2 20 = 0 by linear_combination d4_2_25 + ((-1 : R) * X 2 20) * htwo)
  · exact (show X 2 21 = 0 by
      linear_combination c1 + d3_1_25 + d5_0_23 + d5_2_25 + d7_1_23 + ((1 : R) * X 0 16) * htwo +
        ((-1 : R) * X 2 21) * htwo + ((3 : R) * X 4 23) * htwo + ((-3 : R) * X 9 25) * htwo)
  · exact (show X 2 22 = 0 by
      linear_combination c0 + d8_0_22 + ((-2 : R) * X 0 18) * htwo + ((2 : R) * X 2 22) * htwo)
  · exact (show X 2 23 = 0 by linear_combination d8_0_23 + ((2 : R) * X 2 23) * htwo)
  · exact (show X 2 24 = 0 by linear_combination d8_0_24 + ((2 : R) * X 2 24) * htwo)
  · exact (show X 2 25 = 0 by linear_combination d11_1_25 + ((2 : R) * X 2 25) * htwo)

/-- Every entry of the `3`th row of a derivation all of whose coordinates vanish
is zero. -/
theorem entry_row_3 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hq : ∀ p, quotientCoordinate p X = 0) (hi : ∀ a, X (idealRow a) (idealCol a) = 0)
    (n : Fin 26) : X 3 n = 0 := by
  have htwo : (2 : R) = 0 := by exact_mod_cast CharP.cast_eq_zero R 2
  have hc := quotientCoordinate_entries hq
  have i19 : X 3 0 = 0 := hi 19
  have i16 : X 3 1 = 0 := hi 16
  have c14 : ((1 : ℤ) : R) * X 3 2 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 14
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
  have i12 : X 10 10 = 0 := hi 12
  have c10 : ((1 : ℤ) : R) * X 3 4 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 10
  have d2_3_16 : X 3 5 * ((-3 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 16 + ((0 : ℤ) : R) * X 0 16) =
      ((-3 : ℤ) : R) * X 1 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 3 16
  have i11 : X 1 2 = 0 := hi 11
  have d2_3_18 : X 3 6 * ((-3 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 18 + ((0 : ℤ) : R) * X 0 18) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 3 18
  have d2_3_19 : X 3 7 * ((-3 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 19 + ((0 : ℤ) : R) * X 0 19) =
      ((3 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 3 19
  have i8 : X 0 2 = 0 := hi 8
  have d0_3_23 : X 3 8 * ((3 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 19 23 + ((0 : ℤ) : R) * X 0 23) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 3 23
  have d2_7_23 : X 7 12 * ((2 : ℤ) : R) + X 7 13 * ((-1 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 19 23 + ((0 : ℤ) : R) * X 0 23) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 7 23
  have d4_1_13 : X 1 0 * ((0 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 7 13 + ((0 : ℤ) : R) * X 0 13) =
      ((-3 : ℤ) : R) * X 1 4 + ((0 : ℤ) : R) * X 0 4 :=
    hX.entry 4 1 13
  have i7 : X 1 4 = 0 := hi 7
  have d2_3_20 : X 3 9 * ((-3 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 20 + ((0 : ℤ) : R) * X 0 20) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 3 20
  have c6 : ((1 : ℤ) : R) * X 1 6 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 6
  have d0_3_24 : X 3 10 * ((3 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 19 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 3 24
  have d2_7_24 : X 7 14 * ((3 : ℤ) : R) + X 7 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 19 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 7 24
  have d4_1_14 : X 1 6 * ((3 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 7 14 + ((0 : ℤ) : R) * X 0 14) =
      ((0 : ℤ) : R) * X 0 4 + ((0 : ℤ) : R) * X 0 4 :=
    hX.entry 4 1 14
  have d0_0_20 : X 0 4 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 13 20 + ((0 : ℤ) : R) * X 0 20) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 0 20
  have d1_1_20 : X 1 0 * ((0 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 12 20 + ((-3 : ℤ) : R) * X 13 20) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 1 20
  have d3_3_20 : X 3 11 * ((-3 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 12 20 + ((0 : ℤ) : R) * X 0 20) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 3 20
  have i5 : X 0 4 = 0 := hi 5
  have d6_0_12 : X 0 6 * ((-3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 3 12 + ((0 : ℤ) : R) * X 0 12) =
      ((0 : ℤ) : R) * X 0 6 + ((0 : ℤ) : R) * X 0 6 :=
    hX.entry 6 0 12
  have i3 : X 0 6 = 0 := hi 3
  have d2_3_23 : X 3 12 * ((2 : ℤ) : R) + X 3 13 * ((-1 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 23 + ((0 : ℤ) : R) * X 0 23) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 3 23
  have d2_3_24 : X 3 14 * ((3 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 3 24
  have c5 : ((1 : ℤ) : R) * X 0 9 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 5
  have d1_3_25 : X 3 15 * ((3 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 16 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 3 25
  have d2_5_25 : X 5 17 * ((3 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 16 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 5 25
  have d4_0_17 : X 0 9 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 5 17 + ((0 : ℤ) : R) * X 0 17) =
      ((0 : ℤ) : R) * X 0 4 + ((0 : ℤ) : R) * X 0 4 :=
    hX.entry 4 0 17
  have d3_3_24 : X 3 16 * ((3 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 12 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 3 24
  have d4_4_24 : X 4 18 * ((3 : ℤ) : R) + X 4 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 12 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 4 + ((0 : ℤ) : R) * X 0 4 :=
    hX.entry 4 4 24
  have d5_0_18 : X 0 10 * ((-3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 4 18 + ((0 : ℤ) : R) * X 0 18) =
      ((0 : ℤ) : R) * X 0 5 + ((0 : ℤ) : R) * X 0 5 :=
    hX.entry 5 0 18
  have i1 : X 0 10 = 0 := hi 1
  have d2_3_25 : X 3 17 * ((3 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 3 25
  have d4_3_24 : X 3 18 * ((3 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 4 + ((0 : ℤ) : R) * X 0 4 :=
    hX.entry 4 3 24
  have d2_2_25 : X 2 17 * ((3 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 12 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 2 25
  have d3_0_22 : X 0 12 * ((-2 : ℤ) : R) + X 0 13 * ((1 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 6 22 + ((0 : ℤ) : R) * X 0 22) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 0 22
  have d3_3_25 : X 3 19 * ((3 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 12 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 3 25
  have d7_2_22 : X 2 17 * ((-3 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 6 22 + ((0 : ℤ) : R) * X 0 22) =
      ((0 : ℤ) : R) * X 0 7 + ((0 : ℤ) : R) * X 0 7 :=
    hX.entry 7 2 22
  have i0 : X 0 13 = 0 := hi 0
  have d4_3_25 : X 3 20 * ((3 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 4 + ((0 : ℤ) : R) * X 0 4 :=
    hX.entry 4 3 25
  have c2 : ((1 : ℤ) : R) * X 0 14 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 2
  have d6_0_21 : X 0 14 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 3 21 + ((0 : ℤ) : R) * X 0 21) =
      ((0 : ℤ) : R) * X 0 6 + ((0 : ℤ) : R) * X 0 6 :=
    hX.entry 6 0 21
  have d6_0_22 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 3 22 + ((0 : ℤ) : R) * X 0 22) =
      ((0 : ℤ) : R) * X 0 6 + ((0 : ℤ) : R) * X 0 6 :=
    hX.entry 6 0 22
  have c0 : ((1 : ℤ) : R) * X 0 18 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 0
  have d6_0_23 : X 0 18 * ((-3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 3 23 + ((0 : ℤ) : R) * X 0 23) =
      ((0 : ℤ) : R) * X 0 6 + ((0 : ℤ) : R) * X 0 6 :=
    hX.entry 6 0 23
  have d6_0_24 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 3 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 6 + ((0 : ℤ) : R) * X 0 6 :=
    hX.entry 6 0 24
  have d9_1_25 : X 1 0 * ((0 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 3 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 9 + ((0 : ℤ) : R) * X 0 9 :=
    hX.entry 9 1 25
  fin_cases n
  · exact (show X 3 0 = 0 by linear_combination i19)
  · exact (show X 3 1 = 0 by linear_combination i16)
  · exact (show X 3 2 = 0 by linear_combination c14)
  · exact (show X 3 3 = 0 by
      linear_combination c12 + c13 + d0_5_21 + d0_8_23 + d1_0_10 + d1_3_16 + d1_7_21 + d1_11_23 +
        d2_0_8 + d2_5_16 + i12 + ((2 : R) * X 0 0) * htwo + ((2 : R) * X 3 3) * htwo +
        ((-2 : R) * X 7 7) * htwo + ((-2 : R) * X 10 10) * htwo + ((-2 : R) * X 11 11) * htwo +
        ((-3 : R) * X 16 16) * htwo + ((3 : R) * X 21 21) * htwo + ((3 : R) * X 23 23) * htwo)
  · exact (show X 3 4 = 0 by linear_combination c10)
  · exact (show X 3 5 = 0 by
      linear_combination d2_3_16 + i11 + ((-2 : R) * X 1 2) * htwo + ((2 : R) * X 3 5) * htwo)
  · exact (show X 3 6 = 0 by linear_combination d2_3_18 + ((2 : R) * X 3 6) * htwo)
  · exact (show X 3 7 = 0 by
      linear_combination d2_3_19 + i8 + ((1 : R) * X 0 2) * htwo + ((2 : R) * X 3 7) * htwo)
  · exact (show X 3 8 = 0 by
      linear_combination d0_3_23 + d2_7_23 + d4_1_13 + i7 + ((-2 : R) * X 1 4) * htwo +
        ((-1 : R) * X 3 8) * htwo + ((-1 : R) * X 7 12) * htwo + ((2 : R) * X 7 13) * htwo)
  · exact (show X 3 9 = 0 by linear_combination d2_3_20 + ((2 : R) * X 3 9) * htwo)
  · exact (show X 3 10 = 0 by
      linear_combination c6 + d0_3_24 + d2_7_24 + d4_1_14 + ((-2 : R) * X 1 6) * htwo +
        ((-1 : R) * X 3 10) * htwo)
  · exact (show X 3 11 = 0 by
      linear_combination d0_0_20 + d1_1_20 + d3_3_20 + i5 + ((-2 : R) * X 0 4) * htwo +
        ((2 : R) * X 3 11) * htwo)
  · exact (show X 3 12 = 0 by
      linear_combination d6_0_12 + i3 + ((1 : R) * X 0 6) * htwo + ((-1 : R) * X 3 12) * htwo)
  · exact (show X 3 13 = 0 by
      linear_combination d2_3_23 + ((-1 : R) * X 3 12) * htwo + ((1 : R) * X 3 13) * htwo)
  · exact (show X 3 14 = 0 by linear_combination d2_3_24 + ((-1 : R) * X 3 14) * htwo)
  · exact (show X 3 15 = 0 by
      linear_combination c5 + d1_3_25 + d2_5_25 + d4_0_17 + ((-2 : R) * X 0 9) * htwo +
        ((-1 : R) * X 3 15) * htwo + ((-3 : R) * X 16 25) * htwo)
  · exact (show X 3 16 = 0 by
      linear_combination d3_3_24 + d4_4_24 + d5_0_18 + i1 + ((1 : R) * X 0 10) * htwo +
        ((-1 : R) * X 3 16) * htwo + ((3 : R) * X 12 24) * htwo)
  · exact (show X 3 17 = 0 by linear_combination d2_3_25 + ((-1 : R) * X 3 17) * htwo)
  · exact (show X 3 18 = 0 by linear_combination d4_3_24 + ((-1 : R) * X 3 18) * htwo)
  · exact (show X 3 19 = 0 by
      linear_combination d2_2_25 + d3_0_22 + d3_3_25 + d7_2_22 + i0 + ((1 : R) * X 0 12) * htwo +
        ((-1 : R) * X 0 13) * htwo + ((-1 : R) * X 3 19) * htwo + ((3 : R) * X 12 25) * htwo)
  · exact (show X 3 20 = 0 by linear_combination d4_3_25 + ((-1 : R) * X 3 20) * htwo)
  · exact (show X 3 21 = 0 by
      linear_combination c2 + d6_0_21 + ((-2 : R) * X 0 14) * htwo + ((-1 : R) * X 3 21) * htwo)
  · exact (show X 3 22 = 0 by linear_combination d6_0_22 + ((-1 : R) * X 3 22) * htwo)
  · exact (show X 3 23 = 0 by
      linear_combination c0 + d6_0_23 + ((1 : R) * X 0 18) * htwo + ((-1 : R) * X 3 23) * htwo)
  · exact (show X 3 24 = 0 by linear_combination d6_0_24 + ((-1 : R) * X 3 24) * htwo)
  · exact (show X 3 25 = 0 by linear_combination d9_1_25 + ((-1 : R) * X 3 25) * htwo)

end TauCeti.F4ShortRoot
