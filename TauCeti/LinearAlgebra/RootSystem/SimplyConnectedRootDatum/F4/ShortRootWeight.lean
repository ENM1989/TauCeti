/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.F4.Basic

/-!
# The weight diagram of the short-root representation of type F4

This file enumerates the twenty-six weights, with multiplicity, of the irreducible
representation of type `F₄` with highest weight the fourth fundamental weight `ϖ₄`, in the
Bourbaki numbering where the nodes `0` and `1` are long and the nodes `2` and `3` are short.
The weights are expressed in the fundamental-weight basis `Fin 4 → ℤ`, so the `i`th coordinate
of a weight is its pairing with the `i`th simple coroot.

The nonzero weights are the twenty-four short roots, each with multiplicity one, and the zero
weight has multiplicity two, so it appears twice in the table. The first weight is `ϖ₄`, which
is the highest short root. The table is a weight diagram in the same sense as the minuscule
tables of types `E₆` and `E₇`: the ordering is by decreasing height, and the two zero-weight
entries are adjacent.

The short roots generate the root lattice of `F₄`, which is also its weight lattice, and the
spanning statement `TauCeti.DynkinType.span_range_f4ShortRootWeight_eq_top` records that the
twenty-six weights span the full character lattice `Fin 4 → ℤ`. It is the input that lets the
weight torus of an integral carrier built on this weight diagram be a closed immersion.

## Main declarations

* `TauCeti.DynkinType.f4ShortRootWeight`: the twenty-six weights in fundamental coordinates.
* `TauCeti.DynkinType.f4ShortRootWeight_eq_zero_iff`: the two zero-weight indices.
* `TauCeti.DynkinType.span_range_f4ShortRootWeight_eq_top`: the weights span the character
  lattice.

## References

The node numbering follows Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VIII.
The weights of the twenty-six-dimensional representation are the short roots and the zero weight
twice, as in J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §13,
Exercise 13.12.
-/

public section

namespace TauCeti.DynkinType

/-! ## The weight table -/

/-- **The twenty-six weights, with multiplicity, of the type-`F₄` representation of highest
weight `ϖ₄`.**

Coordinates are pairings with the four Bourbaki-numbered simple coroots. The ordering begins at
`ϖ₄ = (0, 0, 0, 1)`, lists the twenty-four short roots by decreasing height, and places the two
copies of the zero weight at the indices `12` and `13`; no mathematical structure depends on the
ordering. -/
@[expose] def f4ShortRootWeight : Fin 26 → Fin 4 → ℤ := ![
  ![0, 0, 0, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, 1, 0],
  ![-1, 0, 1, 0], ![1, 0, -1, 1], ![-1, 1, -1, 1], ![1, 0, 0, -1],
  ![0, -1, 1, 1], ![-1, 1, 0, -1], ![0, 0, -1, 2], ![0, -1, 2, -1],
  ![0, 0, 0, 0], ![0, 0, 0, 0],
  ![0, 1, -2, 1], ![0, 0, 1, -2], ![1, -1, 0, 1], ![0, 1, -1, -1],
  ![-1, 0, 0, 1], ![1, -1, 1, -1], ![-1, 0, 1, -1], ![1, 0, -1, 0],
  ![-1, 1, -1, 0], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 0, 0, -1]]

/-- The first weight in the table is the fourth fundamental weight `ϖ₄`. -/
@[simp]
theorem f4ShortRootWeight_zero : f4ShortRootWeight 0 = Pi.single 3 1 := by
  decide

/-- The zero weight occurs exactly at the two indices `12` and `13`. -/
theorem f4ShortRootWeight_eq_zero_iff (a : Fin 26) :
    f4ShortRootWeight a = 0 ↔ a = 12 ∨ a = 13 := by
  revert a
  decide +kernel

/-- The last weight in the table is the lowest weight `-ϖ₄`. -/
@[simp]
theorem f4ShortRootWeight_last : f4ShortRootWeight 25 = -Pi.single 3 1 := by
  decide

/-- Distinct indices with nonzero weight carry distinct weights: the short roots have
multiplicity one. -/
theorem f4ShortRootWeight_injOn :
    Set.InjOn f4ShortRootWeight {a | f4ShortRootWeight a ≠ 0} := by
  intro a ha b hb hab
  revert a b
  decide +kernel

/-- Every pairing of a weight with a simple coroot has absolute value at most two. -/
theorem abs_f4ShortRootWeight_le_two (a : Fin 26) (i : Fin 4) :
    |f4ShortRootWeight a i| ≤ 2 := by
  revert a i
  decide +kernel

/-! ## Spanning the character lattice -/

/-- **The twenty-six weights span the full type-`F₄` character lattice.** The four weights at
the top of the table, `ϖ₄` and the three obtained from it by successively subtracting `α₄`,
`α₃` and `α₂`, already form a basis of `Fin 4 → ℤ`. -/
theorem span_range_f4ShortRootWeight_eq_top :
    Submodule.span ℤ (Set.range f4ShortRootWeight) = ⊤ := by
  apply top_unique
  rw [← (Pi.basisFun ℤ (Fin 4)).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  rw [Pi.basisFun_apply]
  let S := Submodule.span ℤ (Set.range f4ShortRootWeight)
  have h (a : Fin 26) : f4ShortRootWeight a ∈ S :=
    Submodule.subset_span (Set.mem_range_self a)
  fin_cases i
  -- In each branch the displayed, kernel-checked identity expresses the corresponding standard
  -- basis vector as an integral combination of weights from the table.
  · change Pi.single (0 : Fin 4) 1 ∈ S
    rw [show Pi.single (0 : Fin 4) 1 = f4ShortRootWeight 3 + f4ShortRootWeight 2 by
      decide +kernel]
    exact S.add_mem (h 3) (h 2)
  · change Pi.single (1 : Fin 4) 1 ∈ S
    rw [show Pi.single (1 : Fin 4) 1 =
        f4ShortRootWeight 2 + f4ShortRootWeight 1 + f4ShortRootWeight 0 by decide +kernel]
    exact S.add_mem (S.add_mem (h 2) (h 1)) (h 0)
  · change Pi.single (2 : Fin 4) 1 ∈ S
    rw [show Pi.single (2 : Fin 4) 1 = f4ShortRootWeight 1 + f4ShortRootWeight 0 by
      decide +kernel]
    exact S.add_mem (h 1) (h 0)
  · change Pi.single (3 : Fin 4) 1 ∈ S
    rw [show Pi.single (3 : Fin 4) 1 = f4ShortRootWeight 0 by decide +kernel]
    exact h 0

end TauCeti.DynkinType
