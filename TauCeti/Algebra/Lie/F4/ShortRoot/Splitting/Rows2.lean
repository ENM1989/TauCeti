/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.IdealCoordinate

/-!
# Rows 7 to 9 of a derivation with vanishing coordinates

A matrix differentiating the invariant symmetric multiplication of the twenty-six-dimensional
module of type `F₄` modulo two, and annihilated by the twenty-six short-root quotient coordinates
and by the twenty-six ideal coordinates, is zero. This file proves that for the entries in rows
7 to 9.

The derivation equations are graded by the weight of the entry they constrain, so each entry is
determined by the few equations of its own weight together with the vanishing coordinates of that
weight; the proof of each entry is that combination. The equations themselves are the entrywise
form `TauCeti.F4ShortRoot.IsDerivation.entry` of the derivation equations, instantiated at the
relevant indices, and each combination is exact up to multiples of two, which vanish in
characteristic two.

## Main results

* `TauCeti.F4ShortRoot.entry_row_7` and its companions up to
  `TauCeti.F4ShortRoot.entry_row_9`: the entries of these rows vanish.
-/

public section

open Matrix

namespace TauCeti.F4ShortRoot

universe u

variable {R : Type u} [CommRing R] [CharP R 2]

/-- Every entry of the `7`th row of a derivation all of whose coordinates vanish
is zero. -/
theorem entry_row_7 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hq : ∀ p, quotientCoordinate p X = 0) (hi : ∀ a, X (idealRow a) (idealCol a) = 0)
    (n : Fin 26) : X 7 n = 0 := by
  have htwo : (2 : R) = 0 := by exact_mod_cast CharP.cast_eq_zero R 2
  have hc := quotientCoordinate_entries hq
  have c18 : ((1 : ℤ) : R) * X 7 0 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 18
  have d0_7_15 : X 7 1 * ((3 : ℤ) : R) + X 7 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 15 + ((0 : ℤ) : R) * X 0 15) =
      ((-3 : ℤ) : R) * X 5 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 7 15
  have i21 : X 5 0 = 0 := hi 21
  have d0_7_17 : X 7 2 * ((3 : ℤ) : R) + X 7 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 17 + ((0 : ℤ) : R) * X 0 17) =
      ((3 : ℤ) : R) * X 3 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 7 17
  have i19 : X 3 0 = 0 := hi 19
  have d0_7_19 : X 7 3 * ((3 : ℤ) : R) + X 7 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 19 + ((0 : ℤ) : R) * X 0 19) =
      ((-3 : ℤ) : R) * X 2 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 7 19
  have i17 : X 2 0 = 0 := hi 17
  have d0_7_20 : X 7 4 * ((3 : ℤ) : R) + X 7 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 20 + ((0 : ℤ) : R) * X 0 20) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 7 20
  have d0_7_21 : X 7 5 * ((3 : ℤ) : R) + X 7 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 21 + ((0 : ℤ) : R) * X 0 21) =
      ((3 : ℤ) : R) * X 1 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 7 21
  have i15 : X 1 0 = 0 := hi 15
  have d0_7_22 : X 7 6 * ((3 : ℤ) : R) + X 7 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 22 + ((0 : ℤ) : R) * X 0 22) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 7 22
  have c13 : ((1 : ℤ) : R) * X 0 0 + ((1 : ℤ) : R) * X 7 7 = 0 := hc 13
  have i13 : X 0 0 = 0 := hi 13
  have d0_7_23 : X 7 8 * ((3 : ℤ) : R) + X 7 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 23 + ((0 : ℤ) : R) * X 0 23) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 7 23
  have c10 : ((1 : ℤ) : R) * X 3 4 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 10
  have d0_5_22 : X 5 6 * ((3 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 21 22 + ((0 : ℤ) : R) * X 0 22) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 5 22
  have d1_3_18 : X 3 4 * ((-3 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 16 18 + ((0 : ℤ) : R) * X 0 18) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 3 18
  have d1_7_22 : X 7 9 * ((3 : ℤ) : R) + X 7 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 21 22 + ((0 : ℤ) : R) * X 0 22) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 7 22
  have d2_5_18 : X 5 6 * ((-3 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 16 18 + ((0 : ℤ) : R) * X 0 18) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 5 18
  have d0_7_24 : X 7 10 * ((3 : ℤ) : R) + X 7 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 7 24
  have c8 : ((1 : ℤ) : R) * X 2 4 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 8
  have d0_5_23 : X 5 8 * ((3 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 21 23 + ((0 : ℤ) : R) * X 0 23) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 5 23
  have d1_2_18 : X 2 4 * ((-3 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 14 18 + ((0 : ℤ) : R) * X 0 18) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 2 18
  have d1_7_23 : X 7 11 * ((3 : ℤ) : R) + X 7 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 21 23 + ((0 : ℤ) : R) * X 0 23) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 7 23
  have d3_5_18 : X 5 8 * ((-3 : ℤ) : R) + X 5 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 14 18 + ((0 : ℤ) : R) * X 0 18) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 5 18
  have d0_7_25 : X 7 12 * ((-1 : ℤ) : R) + X 7 13 * ((2 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 7 25
  have d4_1_13 : X 1 0 * ((0 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 7 13 + ((0 : ℤ) : R) * X 0 13) =
      ((-3 : ℤ) : R) * X 1 4 + ((0 : ℤ) : R) * X 0 4 :=
    hX.entry 4 1 13
  have i7 : X 1 4 = 0 := hi 7
  have c6 : ((1 : ℤ) : R) * X 1 6 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 6
  have d4_1_14 : X 1 6 * ((3 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 7 14 + ((0 : ℤ) : R) * X 0 14) =
      ((0 : ℤ) : R) * X 0 4 + ((0 : ℤ) : R) * X 0 4 :=
    hX.entry 4 1 14
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
  have d1_7_25 : X 7 15 * ((3 : ℤ) : R) + X 7 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 21 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 7 25
  have d2_5_23 : X 5 12 * ((2 : ℤ) : R) + X 5 13 * ((-1 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 16 23 + ((0 : ℤ) : R) * X 0 23) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 5 23
  have d3_3_20 : X 3 11 * ((-3 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 12 20 + ((0 : ℤ) : R) * X 0 20) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 3 20
  have i5 : X 0 4 = 0 := hi 5
  have c4 : ((1 : ℤ) : R) * X 1 8 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 4
  have d4_1_16 : X 1 8 * ((3 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 7 16 + ((0 : ℤ) : R) * X 0 16) =
      ((0 : ℤ) : R) * X 0 4 + ((0 : ℤ) : R) * X 0 4 :=
    hX.entry 4 1 16
  have d0_3_25 : X 3 12 * ((-1 : ℤ) : R) + X 3 13 * ((2 : ℤ) : R) -
        (((3 : ℤ) : R) * X 19 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 3 25
  have d2_7_25 : X 7 17 * ((3 : ℤ) : R) + X 7 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 19 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 7 25
  have d6_0_12 : X 0 6 * ((-3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 3 12 + ((0 : ℤ) : R) * X 0 12) =
      ((0 : ℤ) : R) * X 0 6 + ((0 : ℤ) : R) * X 0 6 :=
    hX.entry 6 0 12
  have i3 : X 0 6 = 0 := hi 3
  have d4_1_18 : X 1 0 * ((0 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 7 18 + ((0 : ℤ) : R) * X 0 18) =
      ((0 : ℤ) : R) * X 0 4 + ((0 : ℤ) : R) * X 0 4 :=
    hX.entry 4 1 18
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
  have d7_2_18 : X 2 12 * ((1 : ℤ) : R) + X 2 13 * ((-2 : ℤ) : R) -
        (((3 : ℤ) : R) * X 6 18 + ((0 : ℤ) : R) * X 0 18) =
      ((0 : ℤ) : R) * X 0 7 + ((0 : ℤ) : R) * X 0 7 :=
    hX.entry 7 2 18
  have i2 : X 0 8 = 0 := hi 2
  have d4_1_20 : X 1 0 * ((0 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 7 20 + ((0 : ℤ) : R) * X 0 20) =
      ((0 : ℤ) : R) * X 0 4 + ((0 : ℤ) : R) * X 0 4 :=
    hX.entry 4 1 20
  have d2_2_24 : X 2 14 * ((3 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 12 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 2 24
  have d3_1_22 : X 1 12 * ((-2 : ℤ) : R) + X 1 13 * ((1 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 9 22 + ((0 : ℤ) : R) * X 0 22) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 1 22
  have d4_1_21 : X 1 12 * ((2 : ℤ) : R) + X 1 13 * ((-1 : ℤ) : R) -
        (((3 : ℤ) : R) * X 7 21 + ((0 : ℤ) : R) * X 0 21) =
      ((0 : ℤ) : R) * X 0 4 + ((0 : ℤ) : R) * X 0 4 :=
    hX.entry 4 1 21
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
  have d4_1_22 : X 1 0 * ((0 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 7 22 + ((0 : ℤ) : R) * X 0 22) =
      ((0 : ℤ) : R) * X 0 4 + ((0 : ℤ) : R) * X 0 4 :=
    hX.entry 4 1 22
  have d4_1_23 : X 1 0 * ((0 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 7 23 + ((0 : ℤ) : R) * X 0 23) =
      ((0 : ℤ) : R) * X 0 4 + ((0 : ℤ) : R) * X 0 4 :=
    hX.entry 4 1 23
  have d6_2_24 : X 2 0 * ((0 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 7 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 6 + ((0 : ℤ) : R) * X 0 6 :=
    hX.entry 6 2 24
  have c0 : ((1 : ℤ) : R) * X 0 18 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 0
  have d6_2_25 : X 2 22 * ((3 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 7 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 6 + ((0 : ℤ) : R) * X 0 6 :=
    hX.entry 6 2 25
  have d8_0_22 : X 0 18 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 2 22 + ((0 : ℤ) : R) * X 0 22) =
      ((0 : ℤ) : R) * X 0 8 + ((0 : ℤ) : R) * X 0 8 :=
    hX.entry 8 0 22
  fin_cases n
  · exact (show X 7 0 = 0 by linear_combination c18)
  · exact (show X 7 1 = 0 by
      linear_combination d0_7_15 + i21 + ((-2 : R) * X 5 0) * htwo + ((-1 : R) * X 7 1) * htwo)
  · exact (show X 7 2 = 0 by
      linear_combination d0_7_17 + i19 + ((1 : R) * X 3 0) * htwo + ((-1 : R) * X 7 2) * htwo)
  · exact (show X 7 3 = 0 by
      linear_combination d0_7_19 + i17 + ((-2 : R) * X 2 0) * htwo + ((-1 : R) * X 7 3) * htwo)
  · exact (show X 7 4 = 0 by linear_combination d0_7_20 + ((-1 : R) * X 7 4) * htwo)
  · exact (show X 7 5 = 0 by
      linear_combination d0_7_21 + i15 + ((1 : R) * X 1 0) * htwo + ((-1 : R) * X 7 5) * htwo)
  · exact (show X 7 6 = 0 by linear_combination d0_7_22 + ((-1 : R) * X 7 6) * htwo)
  · exact (show X 7 7 = 0 by linear_combination c13 + i13 + ((-1 : R) * X 0 0) * htwo)
  · exact (show X 7 8 = 0 by linear_combination d0_7_23 + ((-1 : R) * X 7 8) * htwo)
  · exact (show X 7 9 = 0 by
      linear_combination c10 + d0_5_22 + d1_3_18 + d1_7_22 + d2_5_18 + ((1 : R) * X 3 4) * htwo +
        ((-1 : R) * X 7 9) * htwo + ((-3 : R) * X 16 18) * htwo + ((3 : R) * X 21 22) * htwo)
  · exact (show X 7 10 = 0 by linear_combination d0_7_24 + ((-1 : R) * X 7 10) * htwo)
  · exact (show X 7 11 = 0 by
      linear_combination c8 + d0_5_23 + d1_2_18 + d1_7_23 + d3_5_18 + ((1 : R) * X 2 4) * htwo +
        ((-1 : R) * X 7 11) * htwo + ((3 : R) * X 21 23) * htwo)
  · exact (show X 7 12 = 0 by
      linear_combination d0_7_25 + ((1 : R) * X 7 12) * htwo + ((-1 : R) * X 7 13) * htwo)
  · exact (show X 7 13 = 0 by
      linear_combination d4_1_13 + i7 + ((-2 : R) * X 1 4) * htwo + ((2 : R) * X 7 13) * htwo)
  · exact (show X 7 14 = 0 by
      linear_combination c6 + d4_1_14 + ((-2 : R) * X 1 6) * htwo + ((2 : R) * X 7 14) * htwo)
  · exact (show X 7 15 = 0 by
      linear_combination d0_0_20 + d0_5_25 + d1_1_20 + d1_3_23 + d1_5_24 + d1_7_25 + d2_5_23 +
        d3_3_20 + i5 + ((-2 : R) * X 0 4) * htwo + ((-1 : R) * X 5 12) * htwo +
        ((-1 : R) * X 5 13) * htwo + ((-1 : R) * X 7 15) * htwo + ((-3 : R) * X 16 23) * htwo +
        ((3 : R) * X 21 25) * htwo)
  · exact (show X 7 16 = 0 by
      linear_combination c4 + d4_1_16 + ((-2 : R) * X 1 8) * htwo + ((2 : R) * X 7 16) * htwo)
  · exact (show X 7 17 = 0 by
      linear_combination d0_3_25 + d2_7_25 + d6_0_12 + i3 + ((1 : R) * X 0 6) * htwo +
        ((-1 : R) * X 3 12) * htwo + ((-1 : R) * X 3 13) * htwo + ((-1 : R) * X 7 17) * htwo)
  · exact (show X 7 18 = 0 by linear_combination d4_1_18 + ((2 : R) * X 7 18) * htwo)
  · exact (show X 7 19 = 0 by
      linear_combination d0_2_25 + d3_0_18 + d3_7_25 + d7_2_18 + i2 + ((1 : R) * X 0 8) * htwo +
        ((-1 : R) * X 7 19) * htwo + ((3 : R) * X 17 25) * htwo)
  · exact (show X 7 20 = 0 by linear_combination d4_1_20 + ((2 : R) * X 7 20) * htwo)
  · exact (show X 7 21 = 0 by
      linear_combination d2_2_24 + d3_1_22 + d4_1_21 + d4_4_24 + d5_0_18 + d5_2_22 + i1 +
        ((1 : R) * X 0 10) * htwo + ((2 : R) * X 7 21) * htwo + ((-3 : R) * X 9 22) * htwo +
        ((3 : R) * X 12 24) * htwo)
  · exact (show X 7 22 = 0 by linear_combination d4_1_22 + ((2 : R) * X 7 22) * htwo)
  · exact (show X 7 23 = 0 by linear_combination d4_1_23 + ((2 : R) * X 7 23) * htwo)
  · exact (show X 7 24 = 0 by linear_combination d6_2_24 + ((2 : R) * X 7 24) * htwo)
  · exact (show X 7 25 = 0 by
      linear_combination c0 + d6_2_25 + d8_0_22 + ((-2 : R) * X 0 18) * htwo +
        ((2 : R) * X 7 25) * htwo)

/-- Every entry of the `8`th row of a derivation all of whose coordinates vanish
is zero. -/
theorem entry_row_8 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hq : ∀ p, quotientCoordinate p X = 0) (hi : ∀ a, X (idealRow a) (idealCol a) = 0)
    (n : Fin 26) : X 8 n = 0 := by
  have htwo : (2 : R) = 0 := by exact_mod_cast CharP.cast_eq_zero R 2
  have hc := quotientCoordinate_entries hq
  have i23 : X 8 0 = 0 := hi 23
  have c21 : ((1 : ℤ) : R) * X 8 1 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 21
  have d1_8_14 : X 8 2 * ((-3 : ℤ) : R) + X 8 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 14 + ((0 : ℤ) : R) * X 0 14) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 8 14
  have d1_8_16 : X 8 3 * ((-3 : ℤ) : R) + X 8 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 16 + ((0 : ℤ) : R) * X 0 16) =
      ((3 : ℤ) : R) * X 4 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 8 16
  have i18 : X 4 1 = 0 := hi 18
  have d1_8_18 : X 8 4 * ((-3 : ℤ) : R) + X 8 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 18 + ((0 : ℤ) : R) * X 0 18) =
      ((-3 : ℤ) : R) * X 3 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 8 18
  have i16 : X 3 1 = 0 := hi 16
  have c17 : ((1 : ℤ) : R) * X 4 2 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 17
  have d2_0_5 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 8 5 + ((0 : ℤ) : R) * X 0 5) =
      ((3 : ℤ) : R) * X 4 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 0 5
  have c14 : ((1 : ℤ) : R) * X 3 2 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 14
  have d2_0_6 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 8 6 + ((0 : ℤ) : R) * X 0 6) =
      ((-3 : ℤ) : R) * X 3 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 0 6
  have d1_8_21 : X 8 7 * ((3 : ℤ) : R) + X 8 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 21 + ((0 : ℤ) : R) * X 0 21) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 8 21
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
  have i12 : X 10 10 = 0 := hi 12
  have i13 : X 0 0 = 0 := hi 13
  have d1_8_22 : X 8 9 * ((3 : ℤ) : R) + X 8 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 22 + ((0 : ℤ) : R) * X 0 22) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 8 22
  have d2_0_10 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 8 10 + ((0 : ℤ) : R) * X 0 10) =
      ((-3 : ℤ) : R) * X 1 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 0 10
  have i11 : X 1 2 = 0 := hi 11
  have d1_8_23 : X 8 11 * ((3 : ℤ) : R) + X 8 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 23 + ((0 : ℤ) : R) * X 0 23) =
      ((3 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 8 23
  have i10 : X 0 1 = 0 := hi 10
  have d2_0_12 : X 0 2 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 8 12 + ((0 : ℤ) : R) * X 0 12) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 0 12
  have i8 : X 0 2 = 0 := hi 8
  have d1_8_24 : X 8 12 * ((1 : ℤ) : R) + X 8 13 * ((1 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 8 24
  have d2_0_14 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 8 14 + ((0 : ℤ) : R) * X 0 14) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 0 14
  have d1_8_25 : X 8 15 * ((3 : ℤ) : R) + X 8 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 8 25
  have d2_0_16 : X 0 5 * ((-3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 8 16 + ((0 : ℤ) : R) * X 0 16) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 0 16
  have i4 : X 0 5 = 0 := hi 4
  have d2_0_17 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 8 17 + ((0 : ℤ) : R) * X 0 17) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 0 17
  have d2_0_18 : X 0 6 * ((-3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 8 18 + ((0 : ℤ) : R) * X 0 18) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 0 18
  have i3 : X 0 6 = 0 := hi 3
  have c7 : ((1 : ℤ) : R) * X 0 7 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 7
  have d2_0_19 : X 0 7 * ((-3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 8 19 + ((0 : ℤ) : R) * X 0 19) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 0 19
  have c5 : ((1 : ℤ) : R) * X 0 9 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 5
  have d2_0_20 : X 0 9 * ((-3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 8 20 + ((0 : ℤ) : R) * X 0 20) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 0 20
  have d2_0_21 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 8 21 + ((0 : ℤ) : R) * X 0 21) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 0 21
  have d2_0_22 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 8 22 + ((0 : ℤ) : R) * X 0 22) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 0 22
  have d2_0_23 : X 0 12 * ((2 : ℤ) : R) + X 0 13 * ((-1 : ℤ) : R) -
        (((3 : ℤ) : R) * X 8 23 + ((0 : ℤ) : R) * X 0 23) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 0 23
  have i0 : X 0 13 = 0 := hi 0
  have c2 : ((1 : ℤ) : R) * X 0 14 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 2
  have d2_0_24 : X 0 14 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 8 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 0 24
  have d7_3_25 : X 3 0 * ((0 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 8 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 7 + ((0 : ℤ) : R) * X 0 7 :=
    hX.entry 7 3 25
  fin_cases n
  · exact (show X 8 0 = 0 by linear_combination i23)
  · exact (show X 8 1 = 0 by linear_combination c21)
  · exact (show X 8 2 = 0 by linear_combination d1_8_14 + ((2 : R) * X 8 2) * htwo)
  · exact (show X 8 3 = 0 by
      linear_combination d1_8_16 + i18 + ((1 : R) * X 4 1) * htwo + ((2 : R) * X 8 3) * htwo)
  · exact (show X 8 4 = 0 by
      linear_combination d1_8_18 + i16 + ((-2 : R) * X 3 1) * htwo + ((2 : R) * X 8 4) * htwo)
  · exact (show X 8 5 = 0 by
      linear_combination c17 + d2_0_5 + ((1 : R) * X 4 2) * htwo + ((2 : R) * X 8 5) * htwo)
  · exact (show X 8 6 = 0 by
      linear_combination c14 + d2_0_6 + ((-2 : R) * X 3 2) * htwo + ((2 : R) * X 8 6) * htwo)
  · exact (show X 8 7 = 0 by linear_combination d1_8_21 + ((-1 : R) * X 8 7) * htwo)
  · exact (show X 8 8 = 0 by
      linear_combination c12 + d0_8_23 + d1_0_10 + d1_11_23 + i12 + i13 +
        ((2 : R) * X 0 0) * htwo + ((-1 : R) * X 8 8) * htwo + ((-2 : R) * X 10 10) * htwo +
        ((-2 : R) * X 11 11) * htwo + ((3 : R) * X 23 23) * htwo)
  · exact (show X 8 9 = 0 by linear_combination d1_8_22 + ((-1 : R) * X 8 9) * htwo)
  · exact (show X 8 10 = 0 by
      linear_combination d2_0_10 + i11 + ((-2 : R) * X 1 2) * htwo + ((2 : R) * X 8 10) * htwo)
  · exact (show X 8 11 = 0 by
      linear_combination d1_8_23 + i10 + ((1 : R) * X 0 1) * htwo + ((-1 : R) * X 8 11) * htwo)
  · exact (show X 8 12 = 0 by
      linear_combination d2_0_12 + i8 + ((-2 : R) * X 0 2) * htwo + ((2 : R) * X 8 12) * htwo)
  · exact (show X 8 13 = 0 by
      linear_combination d1_8_24 + d2_0_12 + i8 + ((-2 : R) * X 0 2) * htwo +
        ((1 : R) * X 8 12) * htwo)
  · exact (show X 8 14 = 0 by linear_combination d2_0_14 + ((2 : R) * X 8 14) * htwo)
  · exact (show X 8 15 = 0 by linear_combination d1_8_25 + ((-1 : R) * X 8 15) * htwo)
  · exact (show X 8 16 = 0 by
      linear_combination d2_0_16 + i4 + ((1 : R) * X 0 5) * htwo + ((2 : R) * X 8 16) * htwo)
  · exact (show X 8 17 = 0 by linear_combination d2_0_17 + ((2 : R) * X 8 17) * htwo)
  · exact (show X 8 18 = 0 by
      linear_combination d2_0_18 + i3 + ((1 : R) * X 0 6) * htwo + ((2 : R) * X 8 18) * htwo)
  · exact (show X 8 19 = 0 by
      linear_combination c7 + d2_0_19 + ((1 : R) * X 0 7) * htwo + ((2 : R) * X 8 19) * htwo)
  · exact (show X 8 20 = 0 by
      linear_combination c5 + d2_0_20 + ((1 : R) * X 0 9) * htwo + ((2 : R) * X 8 20) * htwo)
  · exact (show X 8 21 = 0 by linear_combination d2_0_21 + ((2 : R) * X 8 21) * htwo)
  · exact (show X 8 22 = 0 by linear_combination d2_0_22 + ((2 : R) * X 8 22) * htwo)
  · exact (show X 8 23 = 0 by
      linear_combination d2_0_23 + i0 + ((-1 : R) * X 0 12) * htwo + ((2 : R) * X 8 23) * htwo)
  · exact (show X 8 24 = 0 by
      linear_combination c2 + d2_0_24 + ((-2 : R) * X 0 14) * htwo + ((2 : R) * X 8 24) * htwo)
  · exact (show X 8 25 = 0 by linear_combination d7_3_25 + ((2 : R) * X 8 25) * htwo)

/-- Every entry of the `9`th row of a derivation all of whose coordinates vanish
is zero. -/
theorem entry_row_9 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hq : ∀ p, quotientCoordinate p X = 0) (hi : ∀ a, X (idealRow a) (idealCol a) = 0)
    (n : Fin 26) : X 9 n = 0 := by
  have htwo : (2 : R) = 0 := by exact_mod_cast CharP.cast_eq_zero R 2
  have hc := quotientCoordinate_entries hq
  have c20 : ((1 : ℤ) : R) * X 9 0 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 20
  have d0_9_15 : X 9 1 * ((3 : ℤ) : R) + X 9 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 15 + ((0 : ℤ) : R) * X 0 15) =
      ((-3 : ℤ) : R) * X 6 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 9 15
  have i22 : X 6 0 = 0 := hi 22
  have d0_9_17 : X 9 2 * ((3 : ℤ) : R) + X 9 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 17 + ((0 : ℤ) : R) * X 0 17) =
      ((3 : ℤ) : R) * X 4 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 9 17
  have i20 : X 4 0 = 0 := hi 20
  have d0_9_19 : X 9 3 * ((3 : ℤ) : R) + X 9 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 19 + ((0 : ℤ) : R) * X 0 19) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 9 19
  have d0_9_20 : X 9 4 * ((3 : ℤ) : R) + X 9 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 20 + ((0 : ℤ) : R) * X 0 20) =
      ((-3 : ℤ) : R) * X 2 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 9 20
  have i17 : X 2 0 = 0 := hi 17
  have d0_9_21 : X 9 5 * ((3 : ℤ) : R) + X 9 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 21 + ((0 : ℤ) : R) * X 0 21) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 9 21
  have d0_9_22 : X 9 6 * ((3 : ℤ) : R) + X 9 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 22 + ((0 : ℤ) : R) * X 0 22) =
      ((3 : ℤ) : R) * X 1 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 9 22
  have i15 : X 1 0 = 0 := hi 15
  have c15 : ((1 : ℤ) : R) * X 4 3 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 15
  have d0_6_21 : X 6 5 * ((3 : ℤ) : R) + X 6 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 22 21 + ((0 : ℤ) : R) * X 0 21) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 6 21
  have d1_4_16 : X 4 3 * ((-3 : ℤ) : R) + X 4 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 18 16 + ((0 : ℤ) : R) * X 0 16) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 4 16
  have d1_9_21 : X 9 7 * ((3 : ℤ) : R) + X 9 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 22 21 + ((0 : ℤ) : R) * X 0 21) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 9 21
  have d2_6_16 : X 6 5 * ((-3 : ℤ) : R) + X 6 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 18 16 + ((0 : ℤ) : R) * X 0 16) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 6 16
  have d0_9_23 : X 9 8 * ((3 : ℤ) : R) + X 9 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 23 + ((0 : ℤ) : R) * X 0 23) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 9 23
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
  have d1_3_16 : X 3 3 * ((-3 : ℤ) : R) + X 3 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 16 16 + ((0 : ℤ) : R) * X 0 16) =
      ((-3 : ℤ) : R) * X 1 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 3 16
  have d1_7_21 : X 7 7 * ((3 : ℤ) : R) + X 7 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 21 21 + ((0 : ℤ) : R) * X 0 21) =
      ((3 : ℤ) : R) * X 1 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 7 21
  have d1_9_22 : X 9 9 * ((3 : ℤ) : R) + X 9 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 22 22 + ((0 : ℤ) : R) * X 0 22) =
      ((3 : ℤ) : R) * X 1 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 9 22
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
  have i13 : X 0 0 = 0 := hi 13
  have d0_9_24 : X 9 10 * ((3 : ℤ) : R) + X 9 0 * ((0 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 9 24
  have c11 : ((1 : ℤ) : R) * X 2 3 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 11
  have d0_6_23 : X 6 8 * ((3 : ℤ) : R) + X 6 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 22 23 + ((0 : ℤ) : R) * X 0 23) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 6 23
  have d1_9_23 : X 9 11 * ((3 : ℤ) : R) + X 9 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 22 23 + ((0 : ℤ) : R) * X 0 23) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 9 23
  have d3_0_8 : X 0 0 * ((0 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 6 8 + ((0 : ℤ) : R) * X 0 8) =
      ((3 : ℤ) : R) * X 2 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 0 8
  have d0_9_25 : X 9 12 * ((-1 : ℤ) : R) + X 9 13 * ((2 : ℤ) : R) -
        (((0 : ℤ) : R) * X 0 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 9 25
  have d3_1_13 : X 1 0 * ((0 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 9 13 + ((0 : ℤ) : R) * X 0 13) =
      ((-3 : ℤ) : R) * X 1 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 1 13
  have i9 : X 1 3 = 0 := hi 9
  have c9 : ((1 : ℤ) : R) * X 1 5 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 9
  have d3_1_14 : X 1 5 * ((3 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 9 14 + ((0 : ℤ) : R) * X 0 14) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 1 14
  have d0_6_25 : X 6 12 * ((-1 : ℤ) : R) + X 6 13 * ((2 : ℤ) : R) -
        (((3 : ℤ) : R) * X 22 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 6 25
  have d1_9_25 : X 9 15 * ((3 : ℤ) : R) + X 9 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 22 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 1 + ((0 : ℤ) : R) * X 0 1 :=
    hX.entry 1 9 25
  have d3_0_12 : X 0 3 * ((3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 6 12 + ((0 : ℤ) : R) * X 0 12) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 0 12
  have i6 : X 0 3 = 0 := hi 6
  have d3_1_16 : X 1 0 * ((0 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 9 16 + ((0 : ℤ) : R) * X 0 16) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 1 16
  have d0_4_25 : X 4 12 * ((-1 : ℤ) : R) + X 4 13 * ((2 : ℤ) : R) -
        (((3 : ℤ) : R) * X 20 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 4 25
  have d2_9_25 : X 9 17 * ((3 : ℤ) : R) + X 9 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 20 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 2 + ((0 : ℤ) : R) * X 0 2 :=
    hX.entry 2 9 25
  have d5_0_12 : X 0 5 * ((-3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 4 12 + ((0 : ℤ) : R) * X 0 12) =
      ((0 : ℤ) : R) * X 0 5 + ((0 : ℤ) : R) * X 0 5 :=
    hX.entry 5 0 12
  have i4 : X 0 5 = 0 := hi 4
  have c4 : ((1 : ℤ) : R) * X 1 8 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 4
  have d3_1_18 : X 1 8 * ((-3 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 9 18 + ((0 : ℤ) : R) * X 0 18) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 1 18
  have d3_1_19 : X 1 0 * ((0 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 9 19 + ((0 : ℤ) : R) * X 0 19) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 1 19
  have d0_2_25 : X 2 12 * ((-1 : ℤ) : R) + X 2 13 * ((2 : ℤ) : R) -
        (((3 : ℤ) : R) * X 17 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 0 + ((0 : ℤ) : R) * X 0 0 :=
    hX.entry 0 2 25
  have d3_0_18 : X 0 8 * ((-3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 6 18 + ((0 : ℤ) : R) * X 0 18) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 0 18
  have d3_1_20 : X 1 11 * ((-3 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 9 20 + ((0 : ℤ) : R) * X 0 20) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 1 20
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
  have d3_1_21 : X 1 0 * ((0 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 9 21 + ((0 : ℤ) : R) * X 0 21) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 1 21
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
  have d5_2_22 : X 2 14 * ((-3 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 9 22 + ((0 : ℤ) : R) * X 0 22) =
      ((0 : ℤ) : R) * X 0 5 + ((0 : ℤ) : R) * X 0 5 :=
    hX.entry 5 2 22
  have i1 : X 0 10 = 0 := hi 1
  have d3_1_23 : X 1 0 * ((0 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 9 23 + ((0 : ℤ) : R) * X 0 23) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 1 23
  have d5_2_24 : X 2 0 * ((0 : ℤ) : R) + X 2 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 9 24 + ((0 : ℤ) : R) * X 0 24) =
      ((0 : ℤ) : R) * X 0 5 + ((0 : ℤ) : R) * X 0 5 :=
    hX.entry 5 2 24
  have c1 : ((1 : ℤ) : R) * X 0 16 + ((0 : ℤ) : R) * X 0 0 = 0 := hc 1
  have d3_1_25 : X 1 19 * ((3 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((-3 : ℤ) : R) * X 9 25 + ((0 : ℤ) : R) * X 0 25) =
      ((0 : ℤ) : R) * X 0 3 + ((0 : ℤ) : R) * X 0 3 :=
    hX.entry 3 1 25
  have d5_0_23 : X 0 16 * ((-3 : ℤ) : R) + X 0 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 4 23 + ((0 : ℤ) : R) * X 0 23) =
      ((0 : ℤ) : R) * X 0 5 + ((0 : ℤ) : R) * X 0 5 :=
    hX.entry 5 0 23
  have d7_1_23 : X 1 19 * ((-3 : ℤ) : R) + X 1 0 * ((0 : ℤ) : R) -
        (((3 : ℤ) : R) * X 4 23 + ((0 : ℤ) : R) * X 0 23) =
      ((0 : ℤ) : R) * X 0 7 + ((0 : ℤ) : R) * X 0 7 :=
    hX.entry 7 1 23
  fin_cases n
  · exact (show X 9 0 = 0 by linear_combination c20)
  · exact (show X 9 1 = 0 by
      linear_combination d0_9_15 + i22 + ((-2 : R) * X 6 0) * htwo + ((-1 : R) * X 9 1) * htwo)
  · exact (show X 9 2 = 0 by
      linear_combination d0_9_17 + i20 + ((1 : R) * X 4 0) * htwo + ((-1 : R) * X 9 2) * htwo)
  · exact (show X 9 3 = 0 by linear_combination d0_9_19 + ((-1 : R) * X 9 3) * htwo)
  · exact (show X 9 4 = 0 by
      linear_combination d0_9_20 + i17 + ((-2 : R) * X 2 0) * htwo + ((-1 : R) * X 9 4) * htwo)
  · exact (show X 9 5 = 0 by linear_combination d0_9_21 + ((-1 : R) * X 9 5) * htwo)
  · exact (show X 9 6 = 0 by
      linear_combination d0_9_22 + i15 + ((1 : R) * X 1 0) * htwo + ((-1 : R) * X 9 6) * htwo)
  · exact (show X 9 7 = 0 by
      linear_combination c15 + d0_6_21 + d1_4_16 + d1_9_21 + d2_6_16 + ((1 : R) * X 4 3) * htwo +
        ((-1 : R) * X 9 7) * htwo + ((-3 : R) * X 18 16) * htwo + ((3 : R) * X 22 21) * htwo)
  · exact (show X 9 8 = 0 by linear_combination d0_9_23 + ((-1 : R) * X 9 8) * htwo)
  · exact (show X 9 9 = 0 by
      linear_combination c12 + c13 + d0_5_21 + d0_6_22 + d0_8_23 + d1_3_16 + d1_7_21 + d1_9_22 +
        d1_11_23 + d2_0_8 + d2_5_16 + d3_0_6 + i13 + ((3 : R) * X 0 0) * htwo +
        ((3 : R) * X 1 1) * htwo + ((-3 : R) * X 6 6) * htwo + ((-2 : R) * X 7 7) * htwo +
        ((-1 : R) * X 9 9) * htwo + ((-2 : R) * X 11 11) * htwo + ((-3 : R) * X 16 16) * htwo +
        ((3 : R) * X 21 21) * htwo + ((3 : R) * X 22 22) * htwo + ((3 : R) * X 23 23) * htwo)
  · exact (show X 9 10 = 0 by linear_combination d0_9_24 + ((-1 : R) * X 9 10) * htwo)
  · exact (show X 9 11 = 0 by
      linear_combination c11 + d0_6_23 + d1_9_23 + d3_0_8 + ((1 : R) * X 2 3) * htwo +
        ((-3 : R) * X 6 8) * htwo + ((-1 : R) * X 9 11) * htwo + ((3 : R) * X 22 23) * htwo)
  · exact (show X 9 12 = 0 by
      linear_combination d0_9_25 + ((1 : R) * X 9 12) * htwo + ((-1 : R) * X 9 13) * htwo)
  · exact (show X 9 13 = 0 by
      linear_combination d3_1_13 + i9 + ((-2 : R) * X 1 3) * htwo + ((-1 : R) * X 9 13) * htwo)
  · exact (show X 9 14 = 0 by
      linear_combination c9 + d3_1_14 + ((-2 : R) * X 1 5) * htwo + ((-1 : R) * X 9 14) * htwo)
  · exact (show X 9 15 = 0 by
      linear_combination d0_6_25 + d1_9_25 + d3_0_12 + i6 + ((-2 : R) * X 0 3) * htwo +
        ((-1 : R) * X 6 12) * htwo + ((-1 : R) * X 6 13) * htwo + ((-1 : R) * X 9 15) * htwo +
        ((3 : R) * X 22 25) * htwo)
  · exact (show X 9 16 = 0 by linear_combination d3_1_16 + ((-1 : R) * X 9 16) * htwo)
  · exact (show X 9 17 = 0 by
      linear_combination d0_4_25 + d2_9_25 + d5_0_12 + i4 + ((1 : R) * X 0 5) * htwo +
        ((2 : R) * X 4 12) * htwo + ((-1 : R) * X 4 13) * htwo + ((-1 : R) * X 9 17) * htwo)
  · exact (show X 9 18 = 0 by
      linear_combination c4 + d3_1_18 + ((1 : R) * X 1 8) * htwo + ((-1 : R) * X 9 18) * htwo)
  · exact (show X 9 19 = 0 by linear_combination d3_1_19 + ((-1 : R) * X 9 19) * htwo)
  · exact (show X 9 20 = 0 by
      linear_combination d0_2_25 + d3_0_18 + d3_1_20 + d3_7_25 + d4_1_19 + d7_2_18 + i2 +
        ((1 : R) * X 0 8) * htwo + ((-1 : R) * X 9 20) * htwo + ((3 : R) * X 17 25) * htwo)
  · exact (show X 9 21 = 0 by linear_combination d3_1_21 + ((-1 : R) * X 9 21) * htwo)
  · exact (show X 9 22 = 0 by
      linear_combination d2_2_24 + d4_4_24 + d5_0_18 + d5_2_22 + i1 + ((1 : R) * X 0 10) * htwo +
        ((-1 : R) * X 9 22) * htwo + ((3 : R) * X 12 24) * htwo)
  · exact (show X 9 23 = 0 by linear_combination d3_1_23 + ((-1 : R) * X 9 23) * htwo)
  · exact (show X 9 24 = 0 by linear_combination d5_2_24 + ((-1 : R) * X 9 24) * htwo)
  · exact (show X 9 25 = 0 by
      linear_combination c1 + d3_1_25 + d5_0_23 + d7_1_23 + ((1 : R) * X 0 16) * htwo +
        ((3 : R) * X 4 23) * htwo + ((-1 : R) * X 9 25) * htwo)

end TauCeti.F4ShortRoot
