/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.AdmissibleLattice
public import TauCeti.LinearAlgebra.Basis.DiagonalTorus.Basic
public import TauCeti.LinearAlgebra.RootSystem.DiagramPermutations
public import TauCeti.LinearAlgebra.Matrix.Minor

/-!
# The special isogeny of type G2 on the seven-dimensional weight basis

Over a field of characteristic three the pinned group of type `G₂` admits an endomorphism `τ`
exchanging the two root lengths: it raises the parameter of a short simple root subgroup to the
third power and leaves that of a long one alone. It is the *special isogeny*. This file writes
`τ` as the explicit polynomial map `Matrix.g2SpecialIsogeny` of signed `2 × 2` minors, read in the
weight basis of the seven-dimensional module of `TauCeti.Algebra.Lie.G2.ShortRoot.Basic`, and
computes it on the four numbered simple root elements and on the weight torus.

## Where the formula comes from

The type-`G₂` Lie algebra acts on the seven-dimensional module `V`, and in characteristic three
the span `I` of the short root vectors and the short coroots is an ideal of it. The quotient by
`I` is again seven-dimensional, with the six long roots and zero as its weights, and the adjoint
action of a group element on that quotient, read in a basis matched to the weight basis of `V`
through the length-exchanging map on weights, is the special isogeny. The Lie algebra lies in the
skew endomorphisms of `V` for its invariant symmetric form, so every entry of that adjoint action
is a signed sum of `2 × 2` minors of the group element; the seven index pairs and the two
corrections at the middle index are the resulting bookkeeping, recorded in
`Matrix.g2SpecialIsogeny`.

## What is proved here

The four pinning equations, the torus equation and the square relation on the numbered simple root
elements are polynomial identities valid over every commutative ring, and none of them assumes a
characteristic. What needs characteristic three is that the formula preserves products, and that
is not proved here: nothing below shows that the formula is multiplicative, that it carries points
of a group to points of a group, or that its square is the Frobenius on anything other than the
numbered simple root elements.

The carrier built from this representation is not identified with the pinned simply connected
group scheme of type `G₂`, and constructions on it transfer to that scheme only along such an
identification.

## Main definitions

* `Matrix.g2SpecialIsogeny`: the matrix of signed `2 × 2` minors carrying the isogeny, on the seven
  index pairs `Matrix.g2SpecialIsogenyPair` and through the column combinations
  `Matrix.g2SpecialIsogenyColumn`.
* `TauCeti.G2ShortRoot.rootElementMatrix`: the matrix `1 + t X + t² Y` of a numbered simple root
  element, for `X` the integral matrix of the generator and `Y` that of its divided square.
* `TauCeti.G2ShortRoot.specialIsogenyRootIndex` and `TauCeti.G2ShortRoot.specialIsogenyExponent`:
  the length-exchanging map on the numbered simple root indices, the diagram permutation
  `TauCeti.lengthPermRankTwo` on each summand, and the exponent it carries, the squared length of
  the root at the exchanged node.
* `TauCeti.G2ShortRoot.specialIsogenyTorusMap`: the induced map `(s₀, s₁) ↦ (s₁, s₀³)` on torus
  points.

## Main results

* `Matrix.g2SpecialIsogeny_one`, `Matrix.g2SpecialIsogeny_map` and
  `Matrix.g2SpecialIsogeny_diagonal`: the formula fixes the identity, commutes with entrywise ring
  morphisms, and sends diagonal matrices to diagonal matrices.
* `TauCeti.G2ShortRoot.g2SpecialIsogeny_rootElementMatrix_inl_zero` and its three siblings: the
  pinning equations `τ (x_{α₁}(t)) = x_{α₂}(t³)` and `τ (x_{α₂}(t)) = x_{α₁}(t)` together with
  their negative-root counterparts, gathered uniformly in
  `TauCeti.G2ShortRoot.g2SpecialIsogeny_rootElementMatrix`.
* `TauCeti.G2ShortRoot.g2SpecialIsogeny_diagonal_torusCharacter`: on the weight torus the formula
  acts through the length-exchanging map on characters, which
  `TauCeti.G2ShortRoot.torusCharacter_specialIsogenyTorusMap` reads on the character lattice.
* `TauCeti.G2ShortRoot.g2SpecialIsogeny_g2SpecialIsogeny_rootElementMatrix`: the square relation
  `τ ∘ τ = Frob₃` on every numbered simple root element, with
  `TauCeti.G2ShortRoot.rootElementMatrix_map_pow_three` identifying the cubed parameter with the
  entrywise Frobenius in characteristic three.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§12.3 and 13.4.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.
* S. Garibaldi and R. M. Guralnick, *Simple groups stabilizing polynomials*, Forum of Mathematics
  Pi **3** (2015), §6, for the quotient by the short-root ideal in characteristic three.
-/

public section

open Matrix

universe u

namespace Matrix

variable {R : Type u} [CommRing R]

/-- The seven index pairs whose `2 × 2` minors carry the type-`G₂` special isogeny. -/
def g2SpecialIsogenyPair : Fin 7 → Fin 7 × Fin 7 :=
  ![(0, 1), (0, 2), (1, 4), (1, 5), (2, 5), (4, 6), (5, 6)]

@[simp] theorem g2SpecialIsogenyPair_zero : g2SpecialIsogenyPair 0 = (0, 1) := (rfl)
@[simp] theorem g2SpecialIsogenyPair_one : g2SpecialIsogenyPair 1 = (0, 2) := (rfl)
@[simp] theorem g2SpecialIsogenyPair_two : g2SpecialIsogenyPair 2 = (1, 4) := (rfl)
@[simp] theorem g2SpecialIsogenyPair_three : g2SpecialIsogenyPair 3 = (1, 5) := (rfl)
@[simp] theorem g2SpecialIsogenyPair_four : g2SpecialIsogenyPair 4 = (2, 5) := (rfl)
@[simp] theorem g2SpecialIsogenyPair_five : g2SpecialIsogenyPair 5 = (4, 6) := (rfl)
@[simp] theorem g2SpecialIsogenyPair_six : g2SpecialIsogenyPair 6 = (5, 6) := (rfl)

/-- The minors of `g` on a fixed row pair `p` against the `j`-th column combination: the pair
`Matrix.g2SpecialIsogenyPair j`, joined by the pair `(2, 4)` at the middle index `3`. -/
def g2SpecialIsogenyColumn (g : Matrix (Fin 7) (Fin 7) R) (p : Fin 7 × Fin 7) (j : Fin 7) : R :=
  pairMinor g p (g2SpecialIsogenyPair j) + if j = 3 then pairMinor g p (2, 4) else 0

/-- The defining equation of the column combination of minors. -/
theorem g2SpecialIsogenyColumn_def (g : Matrix (Fin 7) (Fin 7) R) (p : Fin 7 × Fin 7)
    (j : Fin 7) :
    g2SpecialIsogenyColumn g p j =
      pairMinor g p (g2SpecialIsogenyPair j) + if j = 3 then pairMinor g p (2, 4) else 0 := (rfl)

/-- **The type-`G₂` matrix of signed `2 × 2` minors.** Its `(i, j)` entry reads the `j`-th column
combination of minors on the row pair `Matrix.g2SpecialIsogenyPair i`, diminished at the middle
index `3` by the same combination taken on the row pair `(0, 6)`. -/
def g2SpecialIsogeny (g : Matrix (Fin 7) (Fin 7) R) : Matrix (Fin 7) (Fin 7) R :=
  Matrix.of fun i j =>
    g2SpecialIsogenyColumn g (g2SpecialIsogenyPair i) j -
      if i = 3 then g2SpecialIsogenyColumn g (0, 6) j else 0

/-- The entrywise formula for the type-`G₂` matrix of signed minors. -/
theorem g2SpecialIsogeny_apply (g : Matrix (Fin 7) (Fin 7) R) (i j : Fin 7) :
    g2SpecialIsogeny g i j =
      g2SpecialIsogenyColumn g (g2SpecialIsogenyPair i) j -
        if i = 3 then g2SpecialIsogenyColumn g (0, 6) j else 0 := (rfl)

/-- The formula commutes with entrywise application of a ring morphism. -/
@[simp]
theorem g2SpecialIsogeny_map {S : Type*} [CommRing S] (f : R →+* S)
    (g : Matrix (Fin 7) (Fin 7) R) :
    g2SpecialIsogeny (g.map f) = (g2SpecialIsogeny g).map f := by
  ext i j
  simp only [Matrix.map_apply, g2SpecialIsogeny_apply, g2SpecialIsogenyColumn_def, pairMinor_map,
    apply_ite f, map_zero, map_add, map_sub]

/-- **The formula sends diagonal matrices to diagonal matrices**, pairing up the entries along
the seven distinguished index pairs. The two corrections at the middle index contribute nothing,
because the pairs they add are distinct from all seven. -/
theorem g2SpecialIsogeny_diagonal (d : Fin 7 → R) :
    g2SpecialIsogeny (Matrix.diagonal d) =
      Matrix.diagonal
        ![d 0 * d 1, d 0 * d 2, d 1 * d 4, d 1 * d 5, d 2 * d 5, d 4 * d 6, d 5 * d 6] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [g2SpecialIsogeny_apply, g2SpecialIsogenyColumn_def, pairMinor_eq]

/-- The formula fixes the identity matrix. -/
@[simp]
theorem g2SpecialIsogeny_one : g2SpecialIsogeny (1 : Matrix (Fin 7) (Fin 7) R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [g2SpecialIsogeny_apply, g2SpecialIsogenyColumn_def, pairMinor_eq]

end Matrix

namespace TauCeti.G2ShortRoot

variable {R : Type u} [CommRing R]

/-! ### The numbered simple root elements as matrices -/

/-- The matrix `1 + t X + t² Y` of the numbered simple root element of parameter `t`, with `X` the
integral matrix of the generator and `Y` that of its divided square. -/
def rootElementMatrix (k : Fin 2 ⊕ Fin 2) (t : R) : Matrix (Fin 7) (Fin 7) R :=
  1 + t • (rootIntMatrix k).map (Int.cast : ℤ → R) +
    t ^ 2 • (rootDividedSquare k).map (Int.cast : ℤ → R)

/-- The defining equation of the numbered simple root element matrix. -/
theorem rootElementMatrix_def (k : Fin 2 ⊕ Fin 2) (t : R) :
    rootElementMatrix k t =
      1 + t • (rootIntMatrix k).map (Int.cast : ℤ → R) +
        t ^ 2 • (rootDividedSquare k).map (Int.cast : ℤ → R) := (rfl)

/-- The short positive root element `x_{α₁}(t)`, written out. -/
theorem rootElementMatrix_inl_zero (t : R) :
    rootElementMatrix (.inl 0) t =
      !![1, t, 0, 0, 0, 0, 0;
         0, 1, 0, 0, 0, 0, 0;
         0, 0, 1, 2 * t, t ^ 2, 0, 0;
         0, 0, 0, 1, t, 0, 0;
         0, 0, 0, 0, 1, 0, 0;
         0, 0, 0, 0, 0, 1, t;
         0, 0, 0, 0, 0, 0, 1] := by
  rw [rootElementMatrix, rootIntMatrix_inl, rootDividedSquare_inl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [raisingMatrix, Matrix.single, mul_comm]

/-- The long positive root element `x_{α₂}(t)`, written out. -/
theorem rootElementMatrix_inl_one (t : R) :
    rootElementMatrix (.inl 1) t =
      !![1, 0, 0, 0, 0, 0, 0;
         0, 1, t, 0, 0, 0, 0;
         0, 0, 1, 0, 0, 0, 0;
         0, 0, 0, 1, 0, 0, 0;
         0, 0, 0, 0, 1, t, 0;
         0, 0, 0, 0, 0, 1, 0;
         0, 0, 0, 0, 0, 0, 1] := by
  rw [rootElementMatrix, rootIntMatrix_inl, rootDividedSquare_inl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [raisingMatrix]

/-- The short negative root element `x_{-α₁}(t)`, written out. -/
theorem rootElementMatrix_inr_zero (t : R) :
    rootElementMatrix (.inr 0) t =
      !![1, 0, 0, 0, 0, 0, 0;
         t, 1, 0, 0, 0, 0, 0;
         0, 0, 1, 0, 0, 0, 0;
         0, 0, t, 1, 0, 0, 0;
         0, 0, t ^ 2, 2 * t, 1, 0, 0;
         0, 0, 0, 0, 0, 1, 0;
         0, 0, 0, 0, 0, t, 1] := by
  rw [rootElementMatrix, rootIntMatrix_inr, rootDividedSquare_inr]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [loweringMatrix, Matrix.single, mul_comm]

/-- The long negative root element `x_{-α₂}(t)`, written out. -/
theorem rootElementMatrix_inr_one (t : R) :
    rootElementMatrix (.inr 1) t =
      !![1, 0, 0, 0, 0, 0, 0;
         0, 1, 0, 0, 0, 0, 0;
         0, t, 1, 0, 0, 0, 0;
         0, 0, 0, 1, 0, 0, 0;
         0, 0, 0, 0, 1, 0, 0;
         0, 0, 0, 0, t, 1, 0;
         0, 0, 0, 0, 0, 0, 1] := by
  rw [rootElementMatrix, rootIntMatrix_inr, rootDividedSquare_inr]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [loweringMatrix]

/-! ### The action on the numbered simple root elements -/

/-- The special isogeny carries the short positive simple root subgroup to the long one and cubes
the parameter: `τ (x_{α₁}(t)) = x_{α₂}(t³)`. -/
@[simp]
theorem g2SpecialIsogeny_rootElementMatrix_inl_zero (t : R) :
    g2SpecialIsogeny (rootElementMatrix (.inl 0) t) = rootElementMatrix (.inl 1) (t ^ 3) := by
  rw [rootElementMatrix_inl_zero, rootElementMatrix_inl_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [g2SpecialIsogeny_apply, g2SpecialIsogenyColumn_def, pairMinor_eq] <;> ring

/-- The special isogeny carries the long positive simple root subgroup to the short one and keeps
the parameter: `τ (x_{α₂}(t)) = x_{α₁}(t)`. -/
@[simp]
theorem g2SpecialIsogeny_rootElementMatrix_inl_one (t : R) :
    g2SpecialIsogeny (rootElementMatrix (.inl 1) t) = rootElementMatrix (.inl 0) t := by
  rw [rootElementMatrix_inl_zero, rootElementMatrix_inl_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [g2SpecialIsogeny_apply, g2SpecialIsogenyColumn_def, pairMinor_eq] <;> ring

/-- The special isogeny on the short negative simple root subgroup:
`τ (x_{-α₁}(t)) = x_{-α₂}(t³)`. -/
@[simp]
theorem g2SpecialIsogeny_rootElementMatrix_inr_zero (t : R) :
    g2SpecialIsogeny (rootElementMatrix (.inr 0) t) = rootElementMatrix (.inr 1) (t ^ 3) := by
  rw [rootElementMatrix_inr_zero, rootElementMatrix_inr_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [g2SpecialIsogeny_apply, g2SpecialIsogenyColumn_def, pairMinor_eq] <;> ring

/-- The special isogeny on the long negative simple root subgroup:
`τ (x_{-α₂}(t)) = x_{-α₁}(t)`. -/
@[simp]
theorem g2SpecialIsogeny_rootElementMatrix_inr_one (t : R) :
    g2SpecialIsogeny (rootElementMatrix (.inr 1) t) = rootElementMatrix (.inr 0) t := by
  rw [rootElementMatrix_inr_zero, rootElementMatrix_inr_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [g2SpecialIsogeny_apply, g2SpecialIsogenyColumn_def, pairMinor_eq] <;> ring

/-- The length-exchanging map on the numbered simple root indices: the length-exchanging diagram
permutation `TauCeti.lengthPermRankTwo` on each of the two summands. -/
def specialIsogenyRootIndex : Fin 2 ⊕ Fin 2 → Fin 2 ⊕ Fin 2
  | .inl i => .inl (lengthPermRankTwo i)
  | .inr i => .inr (lengthPermRankTwo i)

/-- The defining equation of the length-exchanging map on positive indices. -/
theorem specialIsogenyRootIndex_inl (i : Fin 2) :
    specialIsogenyRootIndex (.inl i) = .inl (lengthPermRankTwo i) := (rfl)

/-- The defining equation of the length-exchanging map on negative indices. -/
theorem specialIsogenyRootIndex_inr (i : Fin 2) :
    specialIsogenyRootIndex (.inr i) = .inr (lengthPermRankTwo i) := (rfl)

/-- The length-exchanging map on the numbered simple root indices is an involution. -/
@[simp]
theorem specialIsogenyRootIndex_specialIsogenyRootIndex (k : Fin 2 ⊕ Fin 2) :
    specialIsogenyRootIndex (specialIsogenyRootIndex k) = k := by
  rcases k with i | i
  · rw [specialIsogenyRootIndex_inl, specialIsogenyRootIndex_inl,
      lengthPermRankTwo_lengthPermRankTwo]
  · rw [specialIsogenyRootIndex_inr, specialIsogenyRootIndex_inr,
      lengthPermRankTwo_lengthPermRankTwo]

/-- The exponent of the special isogeny at a numbered simple root index: the squared length of the
simple root at the exchanged node, so three at the short node and one at the long node. -/
def specialIsogenyExponent : Fin 2 ⊕ Fin 2 → ℕ
  | .inl i => (DynkinType.G2.rootLength (lengthPermRankTwo i)).toNat
  | .inr i => (DynkinType.G2.rootLength (lengthPermRankTwo i)).toNat

/-- The defining equation of the exponent on positive indices. -/
theorem specialIsogenyExponent_inl (i : Fin 2) :
    specialIsogenyExponent (.inl i) =
      (DynkinType.G2.rootLength (lengthPermRankTwo i)).toNat := (rfl)

/-- The defining equation of the exponent on negative indices. -/
theorem specialIsogenyExponent_inr (i : Fin 2) :
    specialIsogenyExponent (.inr i) =
      (DynkinType.G2.rootLength (lengthPermRankTwo i)).toNat := (rfl)

/-- **The pinning equations, uniformly.** The special isogeny sends the numbered simple root
element at `k` to the one at the length-exchanged index, with the parameter raised to the exponent
of `k`. -/
theorem g2SpecialIsogeny_rootElementMatrix (k : Fin 2 ⊕ Fin 2) (t : R) :
    g2SpecialIsogeny (rootElementMatrix k t) =
      rootElementMatrix (specialIsogenyRootIndex k) (t ^ specialIsogenyExponent k) := by
  rcases k with i | i <;> fin_cases i <;>
    simp [specialIsogenyRootIndex, specialIsogenyExponent, DynkinType.rootLength_G2]

/-- **The square of the special isogeny cubes the parameter of every numbered simple root
element**: `τ (τ (x_k(t))) = x_k(t³)`. -/
theorem g2SpecialIsogeny_g2SpecialIsogeny_rootElementMatrix (k : Fin 2 ⊕ Fin 2) (t : R) :
    g2SpecialIsogeny (g2SpecialIsogeny (rootElementMatrix k t)) = rootElementMatrix k (t ^ 3) := by
  rcases k with i | i <;> fin_cases i <;> simp

/-- In characteristic three the entrywise Frobenius of a numbered simple root element is the
element at the cubed parameter. -/
theorem rootElementMatrix_map_pow_three [CharP R 3] (k : Fin 2 ⊕ Fin 2) (t : R) :
    (rootElementMatrix k t).map (· ^ 3) = rootElementMatrix k (t ^ 3) := by
  have h3 : (3 : R) = 0 := by exact_mod_cast CharP.cast_eq_zero R 3
  rcases k with i | i <;> fin_cases i <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, rootElementMatrix_inl_zero,
      rootElementMatrix_inl_one, rootElementMatrix_inr_zero, rootElementMatrix_inr_one] <;>
    ext a b <;> fin_cases a <;> fin_cases b <;>
    simp only [Fin.reduceFinMk, map_apply, Fin.isValue, of_apply, cons_val', cons_val,
      cons_val_fin_one, cons_val_one, cons_val_zero] <;>
    first | ring1 | linear_combination (2 * t ^ 3) * h3

/-! ### The action on the weight torus -/

/-- The map induced by the special isogeny on torus points, `(s₀, s₁) ↦ (s₁, s₀³)`: the transpose
of the length-exchanging map on the character lattice. -/
def specialIsogenyTorusMap (s : Fin 2 → Rˣ) : Fin 2 → Rˣ := ![s 1, s 0 ^ 3]

/-- The defining equation of the induced map on torus points. -/
theorem specialIsogenyTorusMap_def (s : Fin 2 → Rˣ) :
    specialIsogenyTorusMap s = ![s 1, s 0 ^ 3] := (rfl)

/-- **The induced map on characters.** Evaluating a character at the length-exchanged point is
evaluating at the original point the character `μ ↦ (3 μ₁, μ₀)`, the transpose of the map the
special isogeny induces on the character lattice. -/
theorem torusCharacter_specialIsogenyTorusMap (s : Fin 2 → Rˣ) (μ : Fin 2 → ℤ) :
    torusCharacter (specialIsogenyTorusMap s) μ = torusCharacter s ![3 * μ 1, μ 0] := by
  have h : ((s 0) ^ (3 : ℕ)) ^ μ 1 = s 0 ^ (3 * μ 1) := by
    rw [← zpow_natCast (s 0) 3, ← _root_.zpow_mul]
    norm_num
  rw [torusCharacter_def, torusCharacter_def, Fin.prod_univ_two, Fin.prod_univ_two,
    specialIsogenyTorusMap_def]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [h, mul_comm]

/-- **The special isogeny on the weight torus.** On the diagonal matrix of the weight characters
of a torus point `s`, the formula returns the diagonal matrix of the weight characters of the
length-exchanged point `(s₁, s₀³)`. -/
theorem g2SpecialIsogeny_diagonal_torusCharacter (s : Fin 2 → Rˣ) :
    g2SpecialIsogeny (Matrix.diagonal fun a => (torusCharacter s (weight a) : R)) =
      Matrix.diagonal fun a => (torusCharacter (specialIsogenyTorusMap s) (weight a) : R) := by
  rw [g2SpecialIsogeny_diagonal]
  refine congrArg Matrix.diagonal (funext fun a => ?_)
  rw [torusCharacter_specialIsogenyTorusMap]
  fin_cases a <;>
    simp only [Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, ← Units.val_mul, ← torusCharacter_add] <;>
    exact congrArg (fun μ : Fin 2 → ℤ => ((torusCharacter s μ : Rˣ) : R))
      (by ext b; fin_cases b <;> simp [weight])

end TauCeti.G2ShortRoot
