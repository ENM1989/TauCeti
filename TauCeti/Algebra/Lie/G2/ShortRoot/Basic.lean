/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Presentation.Serre
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.G2.Length

/-!
# The integral seven-dimensional representation of type G2

This file realizes the Chevalley generators of type `G₂` on the seven-element weight diagram of
the fundamental module `V(ϖ₁)`, whose weights are the six short roots together with zero. In the
fundamental-weight coordinates of `TauCeti.DynkinType.g2Root`, and with Bourbaki's numbering in
which the first simple root `α₁` is short and the second `α₂` is long, the weights are listed as

```text
2α₁ + α₂,  α₁ + α₂,  α₁,  0,  -α₁,  -(α₁ + α₂),  -(2α₁ + α₂),
```

the first being the highest weight `ϖ₁`. On the coordinate vector belonging to a weight, the
Cartan generator `H_i` acts by the `i`-th coordinate of that weight; the lowering generator `F_i`
moves each weight down by `α_i` along the diagram; and the raising generator `E_i` moves it up.
The three-term string `α₁, 0, -α₁` through the zero weight forces a coefficient `2` on one step of
`F₁` and one of `E₁`; it is placed on the step out of the zero weight in both cases, which is what
makes the divided squares `E₁² / 2` and `F₁² / 2` integral matrices.

The resulting integer matrices satisfy the Chevalley--Serre relations for the Cartan matrix
`CartanMatrix.G₂`, whose entry `(i, j)` is the value of the `j`-th simple root on the `i`-th simple
coroot. The universal property of the Serre presentation then gives an explicit integral
seven-dimensional representation of the type-`G₂` Serre Lie algebra. The generators of the short
simple root cube to zero and square to twice an integral matrix; those of the long simple root
square to zero.

No identification with the abstract irreducible highest-weight module is asserted, and nothing
here concerns the group scheme the representation will carry: the carrier built from these
matrices is not identified with the pinned simply connected group scheme of type `G₂`, and
constructions on it transfer to that scheme only along such an identification.

## Main definitions

* `TauCeti.G2ShortRoot.weight`: the seven weights in fundamental-weight coordinates.
* `TauCeti.G2ShortRoot.cartanMatrix`, `raisingMatrix`, and `loweringMatrix`: the integral Cartan,
  raising, and lowering matrices.
* `TauCeti.G2ShortRoot.isSerreSystem`: the Chevalley--Serre relations between them over `ℤ`.
* `TauCeti.G2ShortRoot.serreRepresentation`: the induced representation of the type-`G₂` Serre
  Lie algebra.

## Main results

* `TauCeti.G2ShortRoot.range_weight`: the weights are exactly the short roots and zero.
* `TauCeti.G2ShortRoot.span_range_weight_eq_top`: the weights span the character lattice.
* `TauCeti.G2ShortRoot.raisingMatrix_pow_three` and `loweringMatrix_pow_three`: every generator
  cubes to zero, with `raisingMatrix_one_mul_self` and `loweringMatrix_one_mul_self` recording
  that the long-root generators already square to zero.

## References

The numbering and coordinates follow N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*,
Plate IX. The seven-dimensional representation and its weight diagram follow J. E. Humphreys,
*Introduction to Lie Algebras and Representation Theory*, §22.3, and J. C. Jantzen,
*Representations of Algebraic Groups*, II.2.
-/

public section

open scoped Matrix

namespace TauCeti.G2ShortRoot

open LieAlgebra TauCeti.DynkinType

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ## The weight diagram -/

/-- The seven weights of the fundamental module `V(ϖ₁)` of type `G₂` in fundamental-weight
coordinates: the six short roots and zero, ordered as
`2α₁ + α₂, α₁ + α₂, α₁, 0, -α₁, -(α₁ + α₂), -(2α₁ + α₂)`. -/
def weight : Fin 7 → Fin 2 → ℤ :=
  ![![1, 0], ![-1, 1], ![2, -1], ![0, 0], ![-2, 1], ![1, -1], ![-1, 0]]

/-- The weight table, read entrywise. -/
theorem weight_apply (a : Fin 7) :
    weight a = ![![1, 0], ![-1, 1], ![2, -1], ![0, 0], ![-2, 1], ![1, -1], ![-1, 0]] a := (rfl)

/-- The first listed weight is the highest weight `ϖ₁`. -/
theorem weight_zero : weight 0 = Pi.single 0 1 := by decide

/-- The middle listed weight is zero. -/
theorem weight_three : weight 3 = 0 := by decide

/-- The seven weights are injective in their index. -/
theorem weight_injective : Function.Injective weight := by decide

/-- **The weights are the short roots and zero.** The nonzero weights are exactly the roots of the
pinned type-`G₂` datum of squared length one. -/
theorem range_weight :
    Set.range weight = insert 0 (g2Root '' {k | g2Length k = 1}) := by
  ext v
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_image, Set.mem_ofPred_eq, g2Length_apply,
    g2Root_apply]
  constructor
  · rintro ⟨a, rfl⟩
    fin_cases a
    · exact Or.inr ⟨3, by decide, by decide⟩
    · exact Or.inr ⟨2, by decide, by decide⟩
    · exact Or.inr ⟨0, by decide, by decide⟩
    · exact Or.inl (by decide)
    · exact Or.inr ⟨6, by decide, by decide⟩
    · exact Or.inr ⟨8, by decide, by decide⟩
    · exact Or.inr ⟨9, by decide, by decide⟩
  · rintro (rfl | ⟨k, hk, rfl⟩)
    · exact ⟨3, by decide⟩
    · fin_cases k
      · exact ⟨2, by decide⟩
      · exact absurd hk (by decide)
      · exact ⟨1, by decide⟩
      · exact ⟨0, by decide⟩
      · exact absurd hk (by decide)
      · exact absurd hk (by decide)
      · exact ⟨4, by decide⟩
      · exact absurd hk (by decide)
      · exact ⟨5, by decide⟩
      · exact ⟨6, by decide⟩
      · exact absurd hk (by decide)
      · exact absurd hk (by decide)

/-- **The weights span the full character lattice.** The highest weight is the first fundamental
weight, and it and the next weight sum to the second. -/
theorem span_range_weight_eq_top : Submodule.span ℤ (Set.range weight) = ⊤ := by
  apply top_unique
  rw [← (Pi.basisFun ℤ (Fin 2)).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  rw [Pi.basisFun_apply]
  let S := Submodule.span ℤ (Set.range weight)
  have h (a : Fin 7) : weight a ∈ S := Submodule.subset_span (Set.mem_range_self a)
  fin_cases i
  · change Pi.single (0 : Fin 2) 1 ∈ S
    rw [show Pi.single (0 : Fin 2) 1 = weight 0 by decide +kernel]
    exact h 0
  · change Pi.single (1 : Fin 2) 1 ∈ S
    rw [show Pi.single (1 : Fin 2) 1 = weight 0 + weight 1 by decide +kernel]
    exact S.add_mem (h 0) (h 1)

/-! ## The integral generator matrices -/

/-- The Cartan generator `H_i`, acting on each weight vector by the `i`-th coordinate of its
weight. -/
def cartanMatrix (i : Fin 2) : Matrix (Fin 7) (Fin 7) ℤ :=
  Matrix.diagonal fun a => weight a i

/-- The raising generators `E₁` and `E₂`. -/
def raisingMatrix : Fin 2 → Matrix (Fin 7) (Fin 7) ℤ :=
  ![!![0, 1, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 2, 0, 0, 0;
       0, 0, 0, 0, 1, 0, 0;
       0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 1;
       0, 0, 0, 0, 0, 0, 0],
    !![0, 0, 0, 0, 0, 0, 0;
       0, 0, 1, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 1, 0;
       0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0]]

/-- The lowering generators `F₁` and `F₂`. -/
def loweringMatrix : Fin 2 → Matrix (Fin 7) (Fin 7) ℤ :=
  ![!![0, 0, 0, 0, 0, 0, 0;
       1, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0;
       0, 0, 1, 0, 0, 0, 0;
       0, 0, 0, 2, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 1, 0],
    !![0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0;
       0, 1, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 1, 0, 0;
       0, 0, 0, 0, 0, 0, 0]]

/-- The entrywise formula for the diagonal Cartan generator matrix. -/
@[simp]
theorem cartanMatrix_apply (i : Fin 2) (a b : Fin 7) :
    cartanMatrix i a b = if a = b then weight a i else 0 := by
  classical
  rw [cartanMatrix, Matrix.diagonal_apply]

/-- The short-root raising generator `E₁`, written out. -/
theorem raisingMatrix_zero :
    raisingMatrix 0 =
      !![0, 1, 0, 0, 0, 0, 0;
         0, 0, 0, 0, 0, 0, 0;
         0, 0, 0, 2, 0, 0, 0;
         0, 0, 0, 0, 1, 0, 0;
         0, 0, 0, 0, 0, 0, 0;
         0, 0, 0, 0, 0, 0, 1;
         0, 0, 0, 0, 0, 0, 0] := (rfl)

/-- The long-root raising generator `E₂`, written out. -/
theorem raisingMatrix_one :
    raisingMatrix 1 =
      !![0, 0, 0, 0, 0, 0, 0;
         0, 0, 1, 0, 0, 0, 0;
         0, 0, 0, 0, 0, 0, 0;
         0, 0, 0, 0, 0, 0, 0;
         0, 0, 0, 0, 0, 1, 0;
         0, 0, 0, 0, 0, 0, 0;
         0, 0, 0, 0, 0, 0, 0] := (rfl)

/-- The short-root lowering generator `F₁`, written out. -/
theorem loweringMatrix_zero :
    loweringMatrix 0 =
      !![0, 0, 0, 0, 0, 0, 0;
         1, 0, 0, 0, 0, 0, 0;
         0, 0, 0, 0, 0, 0, 0;
         0, 0, 1, 0, 0, 0, 0;
         0, 0, 0, 2, 0, 0, 0;
         0, 0, 0, 0, 0, 0, 0;
         0, 0, 0, 0, 0, 1, 0] := (rfl)

/-- The long-root lowering generator `F₂`, written out. -/
theorem loweringMatrix_one :
    loweringMatrix 1 =
      !![0, 0, 0, 0, 0, 0, 0;
         0, 0, 0, 0, 0, 0, 0;
         0, 1, 0, 0, 0, 0, 0;
         0, 0, 0, 0, 0, 0, 0;
         0, 0, 0, 0, 0, 0, 0;
         0, 0, 0, 0, 1, 0, 0;
         0, 0, 0, 0, 0, 0, 0] := (rfl)

/-! ## Chevalley--Serre relations -/

/-- The integral generator matrices satisfy the Chevalley--Serre relations of type `G₂`, for the
Cartan matrix whose entry `(i, j)` is the value of the `j`-th simple root on the `i`-th simple
coroot. -/
theorem isSerreSystem :
    IsSerreSystem ℤ CartanMatrix.G₂ cartanMatrix raisingMatrix loweringMatrix where
  lie_H_H := by decide +kernel
  lie_E_F_self := by decide +kernel
  lie_E_F_of_ne := by decide +kernel
  lie_H_E := by decide +kernel
  lie_H_F := by decide +kernel
  ad_pow_lie_E_E := by decide +kernel
  ad_pow_lie_F_F := by decide +kernel

/-- The explicit integral seven-dimensional representation of the type-`G₂` Serre Lie algebra. -/
noncomputable def serreRepresentation :
    Matrix.ToLieAlgebra ℤ CartanMatrix.G₂ →ₗ⁅ℤ⁆ Matrix (Fin 7) (Fin 7) ℤ :=
  serreLift isSerreSystem

/-- The integral Serre representation sends `H_i` to the Cartan generator matrix. -/
@[simp]
theorem serreRepresentation_serreH (i : Fin 2) :
    serreRepresentation (serreH ℤ CartanMatrix.G₂ i) = cartanMatrix i :=
  serreLift_serreH isSerreSystem i

/-- The integral Serre representation sends `E_i` to the raising generator matrix. -/
@[simp]
theorem serreRepresentation_serreE (i : Fin 2) :
    serreRepresentation (serreE ℤ CartanMatrix.G₂ i) = raisingMatrix i :=
  serreLift_serreE isSerreSystem i

/-- The integral Serre representation sends `F_i` to the lowering generator matrix. -/
@[simp]
theorem serreRepresentation_serreF (i : Fin 2) :
    serreRepresentation (serreF ℤ CartanMatrix.G₂ i) = loweringMatrix i :=
  serreLift_serreF isSerreSystem i

/-! ## Nilpotency of the generators -/

/-- Every raising generator cubes to zero. -/
@[simp]
theorem raisingMatrix_pow_three (i : Fin 2) : raisingMatrix i ^ 3 = 0 := by
  revert i; decide

/-- Every lowering generator cubes to zero. -/
@[simp]
theorem loweringMatrix_pow_three (i : Fin 2) : loweringMatrix i ^ 3 = 0 := by
  revert i; decide

/-- The long-root raising generator squares to zero. -/
@[simp]
theorem raisingMatrix_one_mul_self : raisingMatrix 1 * raisingMatrix 1 = 0 := by decide

/-- The long-root lowering generator squares to zero. -/
@[simp]
theorem loweringMatrix_one_mul_self : loweringMatrix 1 * loweringMatrix 1 = 0 := by decide

/-- The short-root raising generator squares to twice a single unit matrix. -/
theorem raisingMatrix_zero_mul_self :
    raisingMatrix 0 * raisingMatrix 0 = 2 • Matrix.single 2 4 1 := by decide

/-- The short-root lowering generator squares to twice a single unit matrix. -/
theorem loweringMatrix_zero_mul_self :
    loweringMatrix 0 * loweringMatrix 0 = 2 • Matrix.single 4 2 1 := by decide

end TauCeti.G2ShortRoot
