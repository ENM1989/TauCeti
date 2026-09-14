/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.QuotientCoordinates
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# The special isogeny of type F4 in characteristic two, on matrices

Over a ring of characteristic two the type-`F4` diagram acquires a length-exchanging symmetry:
the map sending a short root to a long one and a long root to twice a short one is an
automorphism of the diagram once root lengths are ignored, and it is realized by an endomorphism
`τ` of the pinned group, the *special isogeny*, which raises the parameter of a short simple root
subgroup to the second power and leaves that of a long one alone. Its square is the Frobenius,
and the Ree groups of type `²F4` are cut out by the fixed points of its odd powers.

This file builds the matrix formula for `τ` in the twenty-six-dimensional short-root
representation and proves its values on the eight numbered simple root subgroups. The formula is
conjugation followed by reading coordinates: the `(p, q)` entry of `τ g` is the `p`th short-root
quotient coordinate of `g Bq g⁻¹`, where `Bq` is the `q`th representing matrix of
`TauCeti.F4ShortRoot.quotientMatrix`. Conceptually `g` acts by conjugation on the represented
Chevalley algebra, the short-root ideal is stable in characteristic two, and the quotient by it,
matched with the short-root weight basis through the length-exchanging map, is again the
twenty-six-dimensional module; no such structure is constructed here, and the formula is used as
the explicit polynomial map it is.

A divided-power exponential of a simple root generator is an involution in characteristic two,
so the eight pinning equations below are conjugations by a single matrix. Expanding such a
conjugation in the parameter gives five coefficient matrices, and each of them is computed
entrywise from the tables: the identity in degree zero, the image root matrix in degree the
length exponent, its divided square in twice that degree, and zero elsewhere.

Multiplicativity of `τ` is not proved here: it needs the stability of the represented Chevalley
algebra and of its short-root ideal under conjugation by points of the carrier, which is not part
of this file. Nothing below identifies the carrier with the pinned simply connected group scheme
of type `F4`, and constructions made here transfer to that group scheme only along such an
identification.

## Main definitions

* `TauCeti.F4ShortRoot.specialIsogenyMatrix`: the matrix formula for `τ`.
* `TauCeti.F4ShortRoot.isogenyReverse` and `TauCeti.F4ShortRoot.isogenyExponent`: the
  length-exchanging involution of the numbered simple roots, and the exponent it carries.
* `TauCeti.F4ShortRoot.rootElementMatrix` and `TauCeti.F4ShortRoot.rootElementUnit`: the matrix
  `1 + u X + u² X⁽²⁾` of a numbered simple root element, and that matrix as an element of the
  general linear group in characteristic two.

## Main results

* `TauCeti.F4ShortRoot.specialIsogenyMatrix_of_coe_eq`: **the pinning equations**
  `τ (xₖ(u)) = x_{rev k}(u ^ eₖ)` on all eight numbered simple root subgroups, with exponent one
  on the two long simple roots and two on the two short ones; the same equations on the elements
  themselves are `TauCeti.F4ShortRoot.specialIsogenyMatrix_rootElementUnit`.
* `TauCeti.F4ShortRoot.specialIsogenyMatrix_of_coe_eq_diagonal`: **the torus equation**, that a
  group element with diagonal matrix is carried to a diagonal matrix, with each entry a ratio of
  two of the original entries.
* `TauCeti.F4ShortRoot.specialIsogenyMatrix_specialIsogenyMatrix`: **the square relation**
  `τ ∘ τ = Frob₂` on the numbered simple root elements, with
  `TauCeti.F4ShortRoot.rootElementMatrix_map_pow_two` identifying the squared parameter with the
  entrywise Frobenius.
* `TauCeti.F4ShortRoot.rootElementMatrix_mul_self`: a numbered simple root element is an
  involution in characteristic two.
* `TauCeti.F4ShortRoot.exp_mul_mul_exp`: the expansion in the parameter of a matrix placed between
  two divided-power exponentials.

## References

* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.
* R. W. Carter, *Simple Groups of Lie Type*, §12.3 and §13.4.
* J. Tits, *Algebraic and abstract simple groups*, Ann. of Math. **80** (1964), for the groups
  the odd powers of `τ` cut out.
-/

public section

open Matrix

namespace TauCeti.F4ShortRoot

universe u

variable {R : Type u} [CommRing R]

/-! ## Products of the numbered simple root matrices -/

/-- The square of a numbered simple root matrix is twice its divided square. -/
theorem rootMatrix_mul_self (k : Fin 4 ⊕ Fin 4) :
    rootMatrix k * rootMatrix k = (2 : ℤ) • rootDividedSquareMatrix k := by
  cases k with
  | inl i => exact raisingMatrix_mul_self i
  | inr i => exact loweringMatrix_mul_self i

/-- A numbered simple root matrix annihilates its divided square on the left. -/
@[simp]
theorem rootMatrix_mul_rootDividedSquareMatrix (k : Fin 4 ⊕ Fin 4) :
    rootMatrix k * rootDividedSquareMatrix k = 0 := by
  cases k with
  | inl i => exact raisingMatrix_mul_raisingDividedSquareMatrix i
  | inr i => exact loweringMatrix_mul_loweringDividedSquareMatrix i

/-- A numbered simple root matrix annihilates its divided square on the right. -/
@[simp]
theorem rootDividedSquareMatrix_mul_rootMatrix (k : Fin 4 ⊕ Fin 4) :
    rootDividedSquareMatrix k * rootMatrix k = 0 := by
  cases k with
  | inl i => exact raisingDividedSquareMatrix_mul_raisingMatrix i
  | inr i => exact loweringDividedSquareMatrix_mul_loweringMatrix i

/-- A numbered simple root matrix cubes to zero. -/
theorem rootMatrix_mul_mul_self (k : Fin 4 ⊕ Fin 4) :
    rootMatrix k * rootMatrix k * rootMatrix k = 0 := by
  rw [rootMatrix_mul_self, smul_mul_assoc, rootDividedSquareMatrix_mul_rootMatrix, smul_zero]

/-- The divided square of a numbered simple root matrix squares to zero. -/
@[simp]
theorem rootDividedSquareMatrix_mul_self (k : Fin 4 ⊕ Fin 4) :
    rootDividedSquareMatrix k * rootDividedSquareMatrix k = 0 := by
  have h2 : ((2 : ℤ) • rootDividedSquareMatrix k) * ((2 : ℤ) • rootDividedSquareMatrix k) =
      (4 : ℤ) • (rootDividedSquareMatrix k * rootDividedSquareMatrix k) := by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]
    norm_num
  have h : (4 : ℤ) • (rootDividedSquareMatrix k * rootDividedSquareMatrix k) = 0 := by
    rw [← h2, ← rootMatrix_mul_self, ← mul_assoc, rootMatrix_mul_mul_self, zero_mul]
  exact (smul_eq_zero.mp h).resolve_left (by norm_num)

/-! ## The length-exchanging data -/

/-- The length-exchanging involution of the numbered simple roots of type `F4`: the reversal of
the Bourbaki numbering, on the positive and on the negative simple roots. -/
@[expose] def isogenyReverse : Fin 4 ⊕ Fin 4 → Fin 4 ⊕ Fin 4 :=
  Sum.map Fin.revPerm Fin.revPerm

/-- The exponent carried by a numbered simple root under the special isogeny: one on the two long
simple roots, the Bourbaki numbers zero and one, and two on the two short ones. -/
@[expose] def isogenyExponent : Fin 4 ⊕ Fin 4 → ℕ :=
  Sum.elim ![1, 1, 2, 2] ![1, 1, 2, 2]

/-- The exponent is one or two. -/
theorem isogenyExponent_eq_one_or_two (k : Fin 4 ⊕ Fin 4) :
    isogenyExponent k = 1 ∨ isogenyExponent k = 2 := by
  revert k
  decide

/-- The length-exchanging involution is an involution. -/
@[simp]
theorem isogenyReverse_isogenyReverse (k : Fin 4 ⊕ Fin 4) :
    isogenyReverse (isogenyReverse k) = k := by
  revert k
  decide

/-- The two exponents met along the length exchange multiply to two. -/
theorem isogenyExponent_mul_isogenyExponent (k : Fin 4 ⊕ Fin 4) :
    isogenyExponent k * isogenyExponent (isogenyReverse k) = 2 := by
  revert k
  decide

/-! ## The isogeny matrix -/

/-- **The special isogeny of type `F4` in characteristic two, as a matrix formula**: the `(p, q)`
entry of `τ g` is the `p`th short-root quotient coordinate of `g Bq g⁻¹`, where `Bq` is the `q`th
representing matrix. -/
def specialIsogenyMatrix (g : GeneralLinearGroup (Fin 26) R) : Matrix (Fin 26) (Fin 26) R :=
  Matrix.of fun p q => quotientCoordinate p ((g : Matrix (Fin 26) (Fin 26) R) *
    (quotientMatrix q).map (Int.cast : ℤ → R) * (↑g⁻¹ : Matrix (Fin 26) (Fin 26) R))

/-- The entrywise formula for the special isogeny matrix. -/
@[simp]
theorem specialIsogenyMatrix_apply (g : GeneralLinearGroup (Fin 26) R) (p q : Fin 26) :
    specialIsogenyMatrix g p q = quotientCoordinate p ((g : Matrix (Fin 26) (Fin 26) R) *
      (quotientMatrix q).map (Int.cast : ℤ → R) * (↑g⁻¹ : Matrix (Fin 26) (Fin 26) R)) := by
  rw [specialIsogenyMatrix, Matrix.of_apply]

/-! ## Entrywise integer casts -/

/-- Entrywise integer casts turn a matrix product into the product of the casts. -/
private theorem map_intCast_mul (M N : Matrix (Fin 26) (Fin 26) ℤ) :
    (M * N).map (Int.cast : ℤ → R) =
      M.map (Int.cast : ℤ → R) * N.map (Int.cast : ℤ → R) := by
  ext a b
  rw [Matrix.map_apply, Matrix.mul_apply, Matrix.mul_apply, Int.cast_sum]
  exact Finset.sum_congr rfl fun c _ => by rw [Int.cast_mul, Matrix.map_apply, Matrix.map_apply]

/-! ## The numbered simple root elements -/

/-- **A matrix between two divided-power exponentials, expanded in the parameter.** The left and
the right exponential are allowed to have different linear and quadratic terms, so the same
expansion serves both a conjugation and a congruence. -/
theorem exp_mul_mul_exp (X Y X' Y' M : Matrix (Fin 26) (Fin 26) R) (u : R) :
    (1 + u • X + u ^ 2 • Y) * M * (1 + u • X' + u ^ 2 • Y') =
      M + u • (X * M + M * X') + u ^ 2 • (X * M * X' + (Y * M + M * Y')) +
        u ^ 3 • (X * M * Y' + Y * M * X') + u ^ 4 • (Y * M * Y') := by
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm]
  module

/-- The matrix `1 + u X + u² X⁽²⁾` of the numbered simple root element of parameter `u`, with
`X` the integral matrix of the generator and `X⁽²⁾` that of its divided square. -/
def rootElementMatrix (k : Fin 4 ⊕ Fin 4) (u : R) : Matrix (Fin 26) (Fin 26) R :=
  1 + u • (rootMatrix k).map (Int.cast : ℤ → R) +
    u ^ 2 • (rootDividedSquareMatrix k).map (Int.cast : ℤ → R)

/-- The defining equation of the numbered simple root element matrix. -/
theorem rootElementMatrix_def (k : Fin 4 ⊕ Fin 4) (u : R) :
    rootElementMatrix k u =
      1 + u • (rootMatrix k).map (Int.cast : ℤ → R) +
        u ^ 2 • (rootDividedSquareMatrix k).map (Int.cast : ℤ → R) := by
  rw [rootElementMatrix]

/-- **A numbered simple root element is an involution in characteristic two.** -/
theorem rootElementMatrix_mul_self [CharP R 2] (k : Fin 4 ⊕ Fin 4) (u : R) :
    rootElementMatrix k u * rootElementMatrix k u = 1 := by
  rw [rootElementMatrix_def]
  set X := (rootMatrix k).map (Int.cast : ℤ → R) with hXdef
  set Y := (rootDividedSquareMatrix k).map (Int.cast : ℤ → R) with hYdef
  have hX : X * X = 0 := by
    rw [hXdef, ← map_intCast_mul, rootMatrix_mul_self]
    ext a b
    rw [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Int.cast_mul, Matrix.zero_apply,
      show ((2 : ℤ) : R) = 0 by exact_mod_cast CharP.cast_eq_zero R 2, zero_mul]
  have hXY : X * Y = 0 := by
    rw [hXdef, hYdef, ← map_intCast_mul, rootMatrix_mul_rootDividedSquareMatrix,
      Matrix.map_zero _ Int.cast_zero]
  have hYX : Y * X = 0 := by
    rw [hXdef, hYdef, ← map_intCast_mul, rootDividedSquareMatrix_mul_rootMatrix,
      Matrix.map_zero _ Int.cast_zero]
  have hY : Y * Y = 0 := by
    rw [hYdef, ← map_intCast_mul, rootDividedSquareMatrix_mul_self,
      Matrix.map_zero _ Int.cast_zero]
  have hexp := exp_mul_mul_exp X Y X Y 1 u
  simp only [mul_one, one_mul] at hexp
  rw [hexp, hX, hXY, hYX, hY, ← two_smul R X, ← two_smul R Y, CharTwo.two_eq_zero]
  simp

/-! ## The coefficients of the expansion -/

/-- The linear coefficient of the conjugation expansion. -/
private theorem quotientCoordinate_termOne (k : Fin 4 ⊕ Fin 4) (p q : Fin 26) :
    quotientCoordinate p (rootMatrix k * quotientMatrix q + quotientMatrix q * rootMatrix k) ≡
      (if isogenyExponent k = 1 then rootMatrix (isogenyReverse k) p q else 0) [ZMOD 2] := by
  rw [quotientCoordinate_add,
    quotientCoordinate_of_isStep ((isStep_rootMatrix k).mul (isStep_quotientMatrix q)) p,
    quotientCoordinate_of_isStep ((isStep_quotientMatrix q).mul (isStep_rootMatrix k)) p,
    isStep_rootMatrix (isogenyReverse k) p q]
  revert k p q
  decide +kernel

/-- The quadratic coefficient of the conjugation expansion. -/
private theorem quotientCoordinate_termTwo (k : Fin 4 ⊕ Fin 4) (p q : Fin 26) :
    quotientCoordinate p (rootMatrix k * quotientMatrix q * rootMatrix k +
        (rootDividedSquareMatrix k * quotientMatrix q +
          quotientMatrix q * rootDividedSquareMatrix k)) ≡
      (if isogenyExponent k = 1 then rootDividedSquareMatrix (isogenyReverse k) p q
        else rootMatrix (isogenyReverse k) p q) [ZMOD 2] := by
  rw [quotientCoordinate_add, quotientCoordinate_add,
    quotientCoordinate_of_isStep
      (((isStep_rootMatrix k).mul (isStep_quotientMatrix q)).mul (isStep_rootMatrix k)) p,
    quotientCoordinate_of_isStep
      ((isStep_rootDividedSquareMatrix k).mul (isStep_quotientMatrix q)) p,
    quotientCoordinate_of_isStep
      ((isStep_quotientMatrix q).mul (isStep_rootDividedSquareMatrix k)) p,
    isStep_rootMatrix (isogenyReverse k) p q,
    isStep_rootDividedSquareMatrix (isogenyReverse k) p q]
  revert k p q
  decide +kernel

/-- The cubic coefficient of the conjugation expansion vanishes. -/
private theorem quotientCoordinate_termThree (k : Fin 4 ⊕ Fin 4) (p q : Fin 26) :
    quotientCoordinate p (rootMatrix k * quotientMatrix q * rootDividedSquareMatrix k +
      rootDividedSquareMatrix k * quotientMatrix q * rootMatrix k) ≡ 0 [ZMOD 2] := by
  rw [quotientCoordinate_add,
    quotientCoordinate_of_isStep
      (((isStep_rootMatrix k).mul (isStep_quotientMatrix q)).mul
        (isStep_rootDividedSquareMatrix k)) p,
    quotientCoordinate_of_isStep
      (((isStep_rootDividedSquareMatrix k).mul (isStep_quotientMatrix q)).mul
        (isStep_rootMatrix k)) p]
  revert k p q
  decide +kernel

/-- The quartic coefficient of the conjugation expansion. -/
private theorem quotientCoordinate_termFour (k : Fin 4 ⊕ Fin 4) (p q : Fin 26) :
    quotientCoordinate p
        (rootDividedSquareMatrix k * quotientMatrix q * rootDividedSquareMatrix k) ≡
      (if isogenyExponent k = 1 then 0
        else rootDividedSquareMatrix (isogenyReverse k) p q) [ZMOD 2] := by
  rw [quotientCoordinate_of_isStep
      (((isStep_rootDividedSquareMatrix k).mul (isStep_quotientMatrix q)).mul
        (isStep_rootDividedSquareMatrix k)) p,
    isStep_rootDividedSquareMatrix (isogenyReverse k) p q]
  revert k p q
  decide +kernel

/-! ## The pinning equations -/

/-- The numbered simple root element of parameter `u`, as an element of the general linear group:
in characteristic two it is its own inverse. -/
def rootElementUnit [CharP R 2] (k : Fin 4 ⊕ Fin 4) (u : R) : GeneralLinearGroup (Fin 26) R :=
  ⟨rootElementMatrix k u, rootElementMatrix k u, rootElementMatrix_mul_self k u,
    rootElementMatrix_mul_self k u⟩

/-- The matrix of a numbered simple root element of the general linear group. -/
@[simp]
theorem coe_rootElementUnit [CharP R 2] (k : Fin 4 ⊕ Fin 4) (u : R) :
    ((rootElementUnit k u : GeneralLinearGroup (Fin 26) R) : Matrix (Fin 26) (Fin 26) R) =
      rootElementMatrix k u := by
  rw [rootElementUnit]

/-- The matrix of the inverse of a numbered simple root element. This is not a `simp` lemma
because the simp normal form of its left-hand side is the matrix inverse of
`TauCeti.F4ShortRoot.rootElementMatrix`. -/
theorem coe_inv_rootElementUnit [CharP R 2] (k : Fin 4 ⊕ Fin 4) (u : R) :
    (((rootElementUnit k u)⁻¹ : GeneralLinearGroup (Fin 26) R) :
        Matrix (Fin 26) (Fin 26) R) = rootElementMatrix k u := by
  rw [rootElementUnit]
  rfl

/-- **The pinning equations of the special isogeny of type `F4`.** A group element whose matrix is
the numbered simple root element `xₖ(u)` is carried to the numbered simple root element of the
length-exchanged index, with the parameter raised to the length exponent: one on the two long
simple roots and two on the two short ones. -/
theorem specialIsogenyMatrix_of_coe_eq [CharP R 2] {g : GeneralLinearGroup (Fin 26) R}
    (k : Fin 4 ⊕ Fin 4) (u : R)
    (hg : (g : Matrix (Fin 26) (Fin 26) R) = rootElementMatrix k u) :
    specialIsogenyMatrix g =
      rootElementMatrix (isogenyReverse k) (u ^ isogenyExponent k) := by
  have hinv : ((g⁻¹ : GeneralLinearGroup (Fin 26) R) : Matrix (Fin 26) (Fin 26) R) =
      rootElementMatrix k u := by
    have hmul : g * g = 1 := by
      apply Units.ext
      rw [Units.val_mul, hg, rootElementMatrix_mul_self]
      rfl
    rw [inv_eq_of_mul_eq_one_right hmul, hg]
  ext p q
  rw [specialIsogenyMatrix_apply, hg, hinv, rootElementMatrix_def, exp_mul_mul_exp,
    quotientCoordinate_add, quotientCoordinate_add, quotientCoordinate_add,
    quotientCoordinate_add, quotientCoordinate_smul, quotientCoordinate_smul,
    quotientCoordinate_smul, quotientCoordinate_smul]
  simp only [← map_intCast_mul, ← Matrix.map_add _ Int.cast_add, quotientCoordinate_map_intCast]
  rw [(CharP.intCast_eq_intCast R 2).mpr (quotientCoordinate_quotientMatrix p q),
    (CharP.intCast_eq_intCast R 2).mpr (quotientCoordinate_termOne k p q),
    (CharP.intCast_eq_intCast R 2).mpr (quotientCoordinate_termTwo k p q),
    (CharP.intCast_eq_intCast R 2).mpr (quotientCoordinate_termThree k p q),
    (CharP.intCast_eq_intCast R 2).mpr (quotientCoordinate_termFour k p q),
    rootElementMatrix_def]
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.map_apply,
    smul_eq_mul, apply_ite (Int.cast : ℤ → R), Int.cast_one, Int.cast_zero]
  rcases isogenyExponent_eq_one_or_two k with he | he
  · rw [he]
    norm_num
  · rw [he]
    norm_num
    ring

/-- **The pinning equations**, on the numbered simple root elements themselves. -/
@[simp]
theorem specialIsogenyMatrix_rootElementUnit [CharP R 2] (k : Fin 4 ⊕ Fin 4) (u : R) :
    specialIsogenyMatrix (rootElementUnit k u) =
      rootElementMatrix (isogenyReverse k) (u ^ isogenyExponent k) :=
  specialIsogenyMatrix_of_coe_eq k u (coe_rootElementUnit k u)

/-! ## The diagonal torus -/

/-- Entrywise integer casts preserve the step structure. -/
private theorem isStep_map_intCast {M : Matrix (Fin 26) (Fin 26) ℤ} {t : Fin 26 → Fin 26}
    {c : Fin 26 → ℤ} (h : M.IsStep t c) :
    (M.map (Int.cast : ℤ → R)).IsStep t fun b => ((c b : ℤ) : R) := by
  intro a b
  rw [Matrix.map_apply, h a b]
  split_ifs
  · rfl
  · exact Int.cast_zero

/-- Off the diagonal, every entry a quotient coordinate reads from a conjugated representing
matrix has an even coefficient. -/
private theorem torusOffDiagonal (p q : Fin 26) (j : Fin 2) (hpq : p ≠ q)
    (hc : coordinateRow j p = quotientTarget q (coordinateCol j p)) :
    coordinateCoeff j p * quotientCoeff q (coordinateCol j p) ≡ 0 [ZMOD 2] := by
  revert p q j
  decide +kernel

/-- On the diagonal, a quotient coordinate reads its argument at exactly one of its two positions
with an odd coefficient, and at that position the two entries it reads lie in the same row and
column of the representing matrix. -/
private theorem torusDiagonal (p : Fin 26) :
    (coordinateCoeff 1 p = 0 ∧
        coordinateRow 0 p = quotientTarget p (coordinateCol 0 p) ∧
        coordinateCoeff 0 p * quotientCoeff p (coordinateCol 0 p) ≡ 1 [ZMOD 2]) ∨
      (coordinateRow 0 p = coordinateCol 0 p ∧
        quotientCoeff p (coordinateCol 0 p) = 0 ∧
        coordinateRow 1 p = coordinateCol 1 p ∧
        coordinateRow 1 p = quotientTarget p (coordinateCol 1 p) ∧
        coordinateCoeff 1 p * quotientCoeff p (coordinateCol 1 p) ≡ 1 [ZMOD 2]) := by
  revert p
  decide +kernel

/-- **The special isogeny carries the diagonal torus into itself.** A group element whose matrix
is diagonal with unit entries is carried to the diagonal matrix whose `p`th entry is the ratio of
those entries at the two positions where the `p`th quotient coordinate reads its argument. -/
theorem specialIsogenyMatrix_of_coe_eq_diagonal [CharP R 2]
    {g : GeneralLinearGroup (Fin 26) R} (d : Fin 26 → Rˣ)
    (hg : (g : Matrix (Fin 26) (Fin 26) R) = Matrix.diagonal fun a => (d a : R)) :
    specialIsogenyMatrix g =
      Matrix.diagonal fun p =>
        (d (coordinateRow 0 p) : R) * (↑((d (coordinateCol 0 p))⁻¹) : R) := by
  have hinv : ((g⁻¹ : GeneralLinearGroup (Fin 26) R) : Matrix (Fin 26) (Fin 26) R) =
      Matrix.diagonal fun a => (↑((d a)⁻¹) : R) := by
    have hmul : g * (⟨Matrix.diagonal fun a => (↑((d a)⁻¹) : R),
        Matrix.diagonal fun a => (d a : R), by
          rw [Matrix.diagonal_mul_diagonal]
          simp, by
          rw [Matrix.diagonal_mul_diagonal]
          simp⟩ : GeneralLinearGroup (Fin 26) R) = 1 := by
      apply Units.ext
      rw [Units.val_mul, hg]
      change Matrix.diagonal _ * Matrix.diagonal _ = 1
      rw [Matrix.diagonal_mul_diagonal]
      simp
    rw [inv_eq_of_mul_eq_one_right hmul]
  ext p q
  have hstep : ((g : Matrix (Fin 26) (Fin 26) R) * (quotientMatrix q).map (Int.cast : ℤ → R) *
      ((g⁻¹ : GeneralLinearGroup (Fin 26) R) : Matrix (Fin 26) (Fin 26) R)).IsStep
        (quotientTarget q) fun b => (d (quotientTarget q b) : R) *
          ((quotientCoeff q b : ℤ) : R) * (↑((d b)⁻¹) : R) := by
    rw [hg, hinv]
    exact ((Matrix.isStep_diagonal _).mul
      (isStep_map_intCast (isStep_quotientMatrix q))).mul (Matrix.isStep_diagonal _)
  rw [specialIsogenyMatrix_apply, quotientCoordinate_eq_of_isStep hstep]
  rcases eq_or_ne p q with rfl | hpq
  · rw [Matrix.diagonal_apply_eq]
    rcases torusDiagonal p with ⟨h1, hcond, hval⟩ | ⟨h0, hq0, h1, hcond, hval⟩
    · have hterm : (if coordinateRow 1 p = quotientTarget p (coordinateCol 1 p) then
          (coordinateCoeff 1 p : R) * ((d (quotientTarget p (coordinateCol 1 p)) : R) *
            ((quotientCoeff p (coordinateCol 1 p) : ℤ) : R) *
            (↑((d (coordinateCol 1 p))⁻¹) : R)) else 0) = 0 := by
        rw [h1]
        split_ifs <;> simp
      rw [hterm, add_zero, ← hcond]
      have hcast : ((coordinateCoeff 0 p * quotientCoeff p (coordinateCol 0 p) : ℤ) : R) = 1 := by
        rw [(CharP.intCast_eq_intCast R 2).mpr hval, Int.cast_one]
      rw [Int.cast_mul] at hcast
      split_ifs with hc
      · calc (coordinateCoeff 0 p : R) * ((d (coordinateRow 0 p) : R) *
              ((quotientCoeff p (coordinateCol 0 p) : ℤ) : R) * (↑((d (coordinateCol 0 p))⁻¹) : R))
            = ((coordinateCoeff 0 p : R) * ((quotientCoeff p (coordinateCol 0 p) : ℤ) : R)) *
                ((d (coordinateRow 0 p) : R) * (↑((d (coordinateCol 0 p))⁻¹) : R)) := by ring
          _ = (d (coordinateRow 0 p) : R) * (↑((d (coordinateCol 0 p))⁻¹) : R) := by
              rw [hcast, one_mul]
      · exact absurd rfl hc
    · have hunit : ∀ a : Fin 26, (d a : R) * (↑((d a)⁻¹) : R) = 1 := fun a => by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      have hterm0 : (if coordinateRow 0 p = quotientTarget p (coordinateCol 0 p) then
          (coordinateCoeff 0 p : R) * ((d (quotientTarget p (coordinateCol 0 p)) : R) *
            ((quotientCoeff p (coordinateCol 0 p) : ℤ) : R) *
            (↑((d (coordinateCol 0 p))⁻¹) : R)) else 0) = 0 := by
        rw [hq0, Int.cast_zero]
        split_ifs <;> simp
      have hcast : ((coordinateCoeff 1 p * quotientCoeff p (coordinateCol 1 p) : ℤ) : R) = 1 := by
        rw [(CharP.intCast_eq_intCast R 2).mpr hval, Int.cast_one]
      rw [Int.cast_mul] at hcast
      rw [hterm0, zero_add, h0, hunit, ← hcond, h1]
      split_ifs with hc
      · calc (coordinateCoeff 1 p : R) * ((d (coordinateCol 1 p) : R) *
              ((quotientCoeff p (coordinateCol 1 p) : ℤ) : R) *
              (↑((d (coordinateCol 1 p))⁻¹) : R))
            = ((coordinateCoeff 1 p : R) * ((quotientCoeff p (coordinateCol 1 p) : ℤ) : R)) *
                ((d (coordinateCol 1 p) : R) * (↑((d (coordinateCol 1 p))⁻¹) : R)) := by ring
          _ = 1 := by rw [hcast, hunit, one_mul]
      · exact absurd rfl hc
  · rw [Matrix.diagonal_apply_ne _ hpq]
    have key : ∀ j : Fin 2, (if coordinateRow j p = quotientTarget q (coordinateCol j p) then
        (coordinateCoeff j p : R) * ((d (quotientTarget q (coordinateCol j p)) : R) *
          ((quotientCoeff q (coordinateCol j p) : ℤ) : R) *
          (↑((d (coordinateCol j p))⁻¹) : R)) else 0) = 0 := by
      intro j
      split_ifs with hc
      · have h2 : ((coordinateCoeff j p * quotientCoeff q (coordinateCol j p) : ℤ) : R) = 0 := by
          rw [(CharP.intCast_eq_intCast R 2).mpr (torusOffDiagonal p q j hpq hc), Int.cast_zero]
        rw [Int.cast_mul] at h2
        calc (coordinateCoeff j p : R) * ((d (quotientTarget q (coordinateCol j p)) : R) *
              ((quotientCoeff q (coordinateCol j p) : ℤ) : R) *
              (↑((d (coordinateCol j p))⁻¹) : R))
            = ((coordinateCoeff j p : R) * ((quotientCoeff q (coordinateCol j p) : ℤ) : R)) *
                ((d (quotientTarget q (coordinateCol j p)) : R) *
                  (↑((d (coordinateCol j p))⁻¹) : R)) := by ring
          _ = 0 := by rw [h2, zero_mul]
      · rfl
    rw [key 0, key 1, add_zero]

/-! ## The square of the isogeny -/

/-- In characteristic two an integer cast is idempotent for squaring. -/
private theorem intCast_sq [CharP R 2] (z : ℤ) : (z : R) ^ 2 = (z : R) := by
  rw [← Int.cast_pow]
  refine (CharP.intCast_eq_intCast R 2).mpr (Int.ModEq.symm (Int.modEq_iff_dvd.mpr ?_))
  have h : z ^ 2 - z = (z - 1) * (z - 1 + 1) := by ring
  rw [h]
  exact (Int.even_mul_succ_self (z - 1)).two_dvd

/-- **Squaring the entries of a numbered simple root element squares its parameter**, which in
characteristic two is the Frobenius on it. -/
theorem rootElementMatrix_map_pow_two [CharP R 2] (k : Fin 4 ⊕ Fin 4) (u : R) :
    (rootElementMatrix k u).map (· ^ 2) = rootElementMatrix k (u ^ 2) := by
  ext a b
  rw [Matrix.map_apply, rootElementMatrix_def, rootElementMatrix_def]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Matrix.one_apply]
  rw [CharTwo.add_sq, CharTwo.add_sq, mul_pow, mul_pow, intCast_sq, intCast_sq]
  split_ifs
  · rw [one_pow]
  · rw [zero_pow two_ne_zero]

/-- **The square of the special isogeny is the Frobenius**, on the numbered simple root
elements: a group element whose matrix is the image of a numbered simple root element is carried
to the entrywise square of that element. -/
theorem specialIsogenyMatrix_specialIsogenyMatrix [CharP R 2]
    {g h : GeneralLinearGroup (Fin 26) R} (k : Fin 4 ⊕ Fin 4) (u : R)
    (hg : (g : Matrix (Fin 26) (Fin 26) R) = rootElementMatrix k u)
    (hh : (h : Matrix (Fin 26) (Fin 26) R) = specialIsogenyMatrix g) :
    specialIsogenyMatrix h = (rootElementMatrix k u).map (· ^ 2) := by
  rw [specialIsogenyMatrix_of_coe_eq k u hg] at hh
  rw [specialIsogenyMatrix_of_coe_eq (isogenyReverse k) (u ^ isogenyExponent k) hh,
    rootElementMatrix_map_pow_two, ← pow_mul, isogenyReverse_isogenyReverse,
    isogenyExponent_mul_isogenyExponent]

end TauCeti.F4ShortRoot
