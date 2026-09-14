/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.F4.Length

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
* `TauCeti.DynkinType.range_f4ShortRootWeight_eq`: the values of the table are exactly the zero
  weight and the short roots of `F₄`.
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

/-! ## The values are the zero weight and the short roots -/

/-- Each nonzero value of the weight table is a short root of the pinned `F₄` datum, one of the
twenty-four roots `f4Root i` with `f4Length i = 1`. -/
theorem f4ShortRootWeight_ne_zero_iff_exists_shortRoot (a : Fin 26) :
    f4ShortRootWeight a ≠ 0 ↔
      ∃ i : Fin 48, f4Length i = 1 ∧ f4Root i = f4ShortRootWeight a := by
  revert a
  decide +kernel

/-- Every short root of the pinned `F₄` datum occurs as a value of the weight table. -/
theorem exists_f4ShortRootWeight_eq_of_f4Length_eq_one {i : Fin 48} (hi : f4Length i = 1) :
    ∃ a : Fin 26, f4ShortRootWeight a = f4Root i := by
  revert i
  decide +kernel

/-- **The values of the weight table are exactly the zero weight and the short roots of `F₄`.**
The nonzero values are the twenty-four short roots `f4Root i` (those with `f4Length i = 1`), each
occurring once, and the zero weight occurs (with multiplicity two). -/
theorem range_f4ShortRootWeight_eq :
    Set.range f4ShortRootWeight = insert 0 (f4Root '' {i | f4Length i = 1}) := by
  ext v
  constructor
  · rintro ⟨a, rfl⟩
    rcases eq_or_ne (f4ShortRootWeight a) 0 with h | h
    · exact h ▸ Set.mem_insert _ _
    · obtain ⟨i, hi, hiv⟩ := (f4ShortRootWeight_ne_zero_iff_exists_shortRoot a).mp h
      exact Set.mem_insert_of_mem _ ⟨i, hi, hiv⟩
  · rintro (rfl | ⟨i, hi, rfl⟩)
    · exact ⟨12, by decide⟩
    · obtain ⟨a, ha⟩ := exists_f4ShortRootWeight_eq_of_f4Length_eq_one hi
      exact ⟨a, ha⟩

/-! ## Spanning the character lattice -/

/-- Each standard basis vector of the type-`F₄` character lattice is an explicit integral
combination of weights from the table. -/
private theorem pi_single_eq_f4ShortRootWeight_sum : ∀ i : Fin 4,
    (Pi.single i 1 : Fin 4 → ℤ) = ![
      f4ShortRootWeight 3 + f4ShortRootWeight 2,
      f4ShortRootWeight 2 + f4ShortRootWeight 1 + f4ShortRootWeight 0,
      f4ShortRootWeight 1 + f4ShortRootWeight 0,
      f4ShortRootWeight 0] i := by
  decide +kernel

/-- **The twenty-six weights span the full type-`F₄` character lattice.** The four weights at
the top of the table, `ϖ₄` and the three obtained from it by successively subtracting `α₄`,
`α₃` and `α₂`, already form a basis of `Fin 4 → ℤ`. -/
theorem span_range_f4ShortRootWeight_eq_top :
    Submodule.span ℤ (Set.range f4ShortRootWeight) = ⊤ := by
  apply top_unique
  rw [← (Pi.basisFun ℤ (Fin 4)).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  rw [Pi.basisFun_apply]
  have h (a : Fin 26) : f4ShortRootWeight a ∈ Submodule.span ℤ (Set.range f4ShortRootWeight) :=
    Submodule.subset_span (Set.mem_range_self a)
  set S := Submodule.span ℤ (Set.range f4ShortRootWeight) with hS
  rw [pi_single_eq_f4ShortRootWeight_sum i]
  fin_cases i
  · exact S.add_mem (h 3) (h 2)
  · exact S.add_mem (S.add_mem (h 2) (h 1)) (h 0)
  · exact S.add_mem (h 1) (h 0)
  · exact h 0

end TauCeti.DynkinType
