/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Sl2
public import Mathlib.Data.Matrix.PEquiv
public import TauCeti.Algebra.Lie.Presentation.Serre
import TauCeti.Algebra.Lie.GeneralLinear.DiagonalCartan
import TauCeti.Algebra.Lie.Sl2.WeightString

/-!
# Chevalley generators from a minuscule weight table

A minuscule representation of a simply laced simple Lie algebra is determined by its weights: each
weight pairs with every simple coroot to `-1`, `0` or `1`, the simple reflections permute the
weights, and the raising operator at a node moves a weight whose coordinate is `-1` to its
reflection and kills every other weight, the lowering operator dually. Every nonzero entry of the
resulting matrices is `1`, so the representation needs no structure constants.

This file packages that data as `TauCeti.MinusculeWeightTable` and builds from it the three
families of integral matrices, proves they are an `sl₂` triple at each node and satisfy the Serre
relations, and lifts them to a representation of the Serre presentation. A type-specific carrier
then supplies only its weight table and reads the whole construction off.

The Cartan matrix is required to be symmetric with diagonal `2` and off-diagonal entries `0` or
`-1`, which is the simply laced condition; the coordinates are pairings with simple coroots, so
the reflection equation reads `wt (s_i a) j = wt a j - wt a i * CM i j`.

## Main declarations

* `TauCeti.MinusculeWeightTable`: the weight-table data and the conditions on it.
* `TauCeti.MinusculeWeightTable.raisingMatrix`, `loweringMatrix` and `cartanGeneratorMatrix`: the
  integral Chevalley generators the table names.
* `TauCeti.MinusculeWeightTable.serreRepresentation`: the representation of the Serre presentation
  they define.

## Main results

* `TauCeti.MinusculeWeightTable.raisingMatrix_apply`, `loweringMatrix_apply` and
  `cartanGeneratorMatrix_apply`: their entry formulas.
* `TauCeti.MinusculeWeightTable.raisingMatrix_pow_two` and `loweringMatrix_pow_two`: the raising
  and lowering matrices square to zero.
* `TauCeti.MinusculeWeightTable.isSl2Triple`: the three matrices at a node are an `sl₂` triple.
* `TauCeti.MinusculeWeightTable.isSerreSystem`: they satisfy the Serre relations.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §13.4, for the
  minuscule-orbit description of these representations.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, for the numbering conventions.
-/

public section

open scoped Matrix

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

/-- **A minuscule weight table for a simply laced Cartan matrix.** The weights are recorded in
simple-coroot coordinates, so `weight a i` is the pairing of the `a`-th weight with the `i`-th
simple coroot, and the simple reflection at `i` acts on the table by `reflection i`. -/
structure MinusculeWeightTable (B ι : Type*) where
  /-- The Cartan matrix, with the root index second. -/
  cartanMatrix : Matrix B B ℤ
  /-- The weights, in simple-coroot coordinates. -/
  weight : ι → B → ℤ
  /-- The permutation of the table induced by the `i`-th simple reflection. -/
  reflection : B → ι → ι
  /-- The Cartan matrix is symmetric. -/
  cartanMatrix_comm : ∀ i j, cartanMatrix j i = cartanMatrix i j
  /-- The Cartan matrix has diagonal entries `2`. -/
  cartanMatrix_self : ∀ i, cartanMatrix i i = 2
  /-- The diagram is simply laced: an off-diagonal entry is `0` or `-1`. -/
  cartanMatrix_eq_zero_or_eq_neg_one :
    ∀ i j, i ≠ j → cartanMatrix i j = 0 ∨ cartanMatrix i j = -1
  /-- Minusculeness: every coordinate of every weight is `-1`, `0` or `1`. -/
  weight_eq_neg_one_or_eq_zero_or_eq_one :
    ∀ a i, weight a i = -1 ∨ weight a i = 0 ∨ weight a i = 1
  /-- The reflection equation `wt (s_i a) j = wt a j - wt a i * CM i j`. -/
  weight_reflection :
    ∀ i a j, weight (reflection i a) j = weight a j - weight a i * cartanMatrix i j
  /-- Distinct indices name distinct weights. -/
  weight_injective : Function.Injective weight
  /-- Every node has a weight of coordinate `-1`, so its Cartan generator is nonzero. -/
  exists_weight_eq_neg_one : ∀ i, ∃ a, weight a i = -1

namespace MinusculeWeightTable

variable {B ι : Type*} (T : MinusculeWeightTable B ι)

/-! ## The reflected weights -/

/-- A simple reflection negates the corresponding simple-coroot coordinate. -/
theorem weight_reflection_self (i : B) (a : ι) :
    T.weight (T.reflection i a) i = -T.weight a i := by
  rw [T.weight_reflection, T.cartanMatrix_self]
  ring

/-- A simple reflection is an involution on the table. -/
theorem reflection_apply_apply (i : B) (a : ι) : T.reflection i (T.reflection i a) = a := by
  apply T.weight_injective
  funext j
  rw [T.weight_reflection i (T.reflection i a) j, T.weight_reflection i a j,
    T.weight_reflection_self]
  ring

/-- A reflection at a node orthogonal to `i` leaves the `i`-th coordinate alone. -/
theorem weight_reflection_of_cartanMatrix_eq_zero (i j : B) (a : ι)
    (hij : T.cartanMatrix i j = 0) :
    T.weight (T.reflection i a) j = T.weight a j := by
  rw [T.weight_reflection, hij]
  ring

/-- Reflections at two orthogonal nodes commute on the table. -/
theorem reflection_comm_of_cartanMatrix_eq_zero (i j : B) (a : ι)
    (hij : T.cartanMatrix i j = 0) :
    T.reflection i (T.reflection j a) = T.reflection j (T.reflection i a) := by
  have hji : T.cartanMatrix j i = 0 := by rw [T.cartanMatrix_comm, hij]
  apply T.weight_injective
  funext k
  rw [T.weight_reflection i (T.reflection j a) k, T.weight_reflection j (T.reflection i a) k,
    T.weight_reflection j a i, T.weight_reflection i a j, T.weight_reflection j a k,
    T.weight_reflection i a k, hij, hji]
  ring

/-! ## The raising and lowering targets -/

/-- The target of the `i`-th raising operator on a weight-basis vector, when nonzero. -/
private def raisingTarget (i : B) (a : ι) : Option ι :=
  if T.weight a i = -1 then some (T.reflection i a) else none

/-- The target of the `i`-th lowering operator on a weight-basis vector, when nonzero. -/
private def loweringTarget (i : B) (a : ι) : Option ι :=
  if T.weight a i = 1 then some (T.reflection i a) else none

/-- Simple reflection restricted to the weights on which the raising operator is nonzero. -/
private def raisingPEquiv (i : B) : ι ≃. ι where
  toFun := T.raisingTarget i
  invFun := T.loweringTarget i
  inv a b := by
    have h :
        (T.weight b i = 1 ∧ T.reflection i b = a) ↔
          (T.weight a i = -1 ∧ T.reflection i a = b) := by
      constructor
      · rintro ⟨hb, rfl⟩
        exact ⟨by rw [T.weight_reflection_self]; omega, T.reflection_apply_apply i b⟩
      · rintro ⟨ha, rfl⟩
        exact ⟨by rw [T.weight_reflection_self]; omega, T.reflection_apply_apply i a⟩
    simpa [raisingTarget, loweringTarget] using h

@[simp]
private theorem raisingTarget_eq_some_iff (i : B) (a b : ι) :
    T.raisingTarget i a = some b ↔ T.weight a i = -1 ∧ b = T.reflection i a := by
  simp [raisingTarget, eq_comm]

@[simp]
private theorem loweringTarget_eq_some_iff (i : B) (a b : ι) :
    T.loweringTarget i a = some b ↔ T.weight a i = 1 ∧ b = T.reflection i a := by
  simp [loweringTarget, eq_comm]

private theorem raisingTarget_bind_loweringTarget_of_cartan_eq_zero (i j : B)
    (hij : T.cartanMatrix i j = 0) (a : ι) :
    (T.loweringTarget j a).bind (T.raisingTarget i) =
      (T.raisingTarget i a).bind (T.loweringTarget j) := by
  have hji : T.cartanMatrix j i = 0 := by rw [T.cartanMatrix_comm, hij]
  by_cases hi : T.weight a i = -1
  · by_cases hj : T.weight a j = 1
    · simp [raisingTarget, loweringTarget, hi, hj,
        T.weight_reflection_of_cartanMatrix_eq_zero i j a hij,
        T.weight_reflection_of_cartanMatrix_eq_zero j i a hji,
        T.reflection_comm_of_cartanMatrix_eq_zero i j a hij]
    · simp [raisingTarget, loweringTarget, hi, hj,
        T.weight_reflection_of_cartanMatrix_eq_zero i j a hij]
  · by_cases hj : T.weight a j = 1
    · simp [raisingTarget, loweringTarget, hi, hj,
        T.weight_reflection_of_cartanMatrix_eq_zero j i a hji]
    · simp [raisingTarget, loweringTarget, hi, hj]

private theorem raisingTarget_bind_loweringTarget_of_cartan_eq_neg_one (i j : B)
    (hij : T.cartanMatrix i j = -1) (a : ι) :
    (T.loweringTarget j a).bind (T.raisingTarget i) =
      (T.raisingTarget i a).bind (T.loweringTarget j) := by
  have hi_lower : -1 ≤ T.weight a i := by
    rcases T.weight_eq_neg_one_or_eq_zero_or_eq_one a i with hi | hi | hi <;> omega
  have hj_upper : T.weight a j ≤ 1 := by
    rcases T.weight_eq_neg_one_or_eq_zero_or_eq_one a j with hj | hj | hj <;> omega
  have hji : T.cartanMatrix j i = -1 := by rw [T.cartanMatrix_comm, hij]
  have hleft : (T.loweringTarget j a).bind (T.raisingTarget i) = none := by
    by_cases hj : T.weight a j = 1
    · have href : T.weight (T.reflection j a) i ≠ -1 := by
        rw [T.weight_reflection, hj, hji]
        omega
      simp [loweringTarget, raisingTarget, hj, href]
    · simp [loweringTarget, hj]
  have hright : (T.raisingTarget i a).bind (T.loweringTarget j) = none := by
    by_cases hi : T.weight a i = -1
    · have href : T.weight (T.reflection i a) j ≠ 1 := by
        rw [T.weight_reflection, hi, hij]
        omega
      simp [raisingTarget, loweringTarget, hi, href]
    · simp [raisingTarget, hi]
  rw [hleft, hright]

private theorem raisingTarget_bind_loweringTarget_of_ne (i j : B) (hij : i ≠ j) (a : ι) :
    (T.loweringTarget j a).bind (T.raisingTarget i) =
      (T.raisingTarget i a).bind (T.loweringTarget j) := by
  rcases T.cartanMatrix_eq_zero_or_eq_neg_one i j hij with hA | hA
  · exact T.raisingTarget_bind_loweringTarget_of_cartan_eq_zero i j hA a
  · exact T.raisingTarget_bind_loweringTarget_of_cartan_eq_neg_one i j hA a

/-! ## The Chevalley generators -/

variable [DecidableEq ι]

/-- The raising matrix of the `i`-th simple root on the integral weight basis. -/
def raisingMatrix (i : B) : Matrix ι ι ℤ :=
  (T.raisingPEquiv i).symm.toMatrix

/-- The lowering matrix of the `i`-th simple root on the integral weight basis. -/
def loweringMatrix (i : B) : Matrix ι ι ℤ :=
  (T.raisingPEquiv i).toMatrix

/-- The diagonal matrix of the `i`-th simple coroot on the integral weight basis. -/
def cartanGeneratorMatrix (i : B) : Matrix ι ι ℤ :=
  Matrix.diagonal (fun b ↦ T.weight b i)

private theorem pEquivMatrix_apply (e : ι ≃. ι) (a b : ι) (p : Prop)
    [Decidable p] (h : b ∈ e a ↔ p) :
    (e.toMatrix : Matrix ι ι ℤ) a b = if p then 1 else 0 := by
  simp only [PEquiv.toMatrix_apply]
  exact if_congr h rfl rfl

/-- The entry formula for a simple raising matrix. -/
@[simp]
theorem raisingMatrix_apply (i : B) (a b : ι) :
    T.raisingMatrix i a b =
      if T.weight b i = -1 ∧ a = T.reflection i b then 1 else 0 := by
  rw [raisingMatrix]
  apply pEquivMatrix_apply
  rw [PEquiv.mem_iff_mem]
  simp [raisingPEquiv, raisingTarget, eq_comm]

/-- The entry formula for a simple lowering matrix. -/
@[simp]
theorem loweringMatrix_apply (i : B) (a b : ι) :
    T.loweringMatrix i a b =
      if T.weight b i = 1 ∧ a = T.reflection i b then 1 else 0 := by
  rw [loweringMatrix]
  apply pEquivMatrix_apply
  rw [← PEquiv.mem_iff_mem]
  simp only [raisingPEquiv, PEquiv.symm]
  simp [loweringTarget, eq_comm]

/-- The entry formula for a simple Cartan generator matrix. -/
@[simp]
theorem cartanGeneratorMatrix_apply (i : B) (a b : ι) :
    T.cartanGeneratorMatrix i a b = if a = b then T.weight b i else 0 := by
  rw [cartanGeneratorMatrix, Matrix.diagonal_apply]
  split_ifs with h
  · subst b
    rfl
  · rfl

/-! ## The Serre relations -/

variable [Fintype ι]

/-- **The raising matrix at each node squares to zero.** The raising operator carries a weight of
coordinate `-1` to its reflection, whose coordinate is `1`, and kills every weight of coordinate
`1`, so two raising steps never compose. -/
@[simp]
theorem raisingMatrix_pow_two (i : B) : T.raisingMatrix i ^ 2 = 0 := by
  ext a b
  simp only [pow_two, Matrix.mul_apply, T.raisingMatrix_apply, Matrix.zero_apply]
  by_cases hb : T.weight b i = -1
  · simp [hb, T.weight_reflection_self]
  · simp [hb]

/-- **The lowering matrix at each node squares to zero**, dually to the raising matrix. -/
@[simp]
theorem loweringMatrix_pow_two (i : B) : T.loweringMatrix i ^ 2 = 0 := by
  ext a b
  simp only [pow_two, Matrix.mul_apply, T.loweringMatrix_apply, Matrix.zero_apply]
  by_cases hb : T.weight b i = 1
  · simp [hb, T.weight_reflection_self]
  · simp [hb]



private theorem lie_raisingMatrix_loweringMatrix_of_ne (i j : B) (hij : i ≠ j) :
    ⁅T.raisingMatrix i, T.loweringMatrix j⁆ = 0 := by
  rw [Ring.lie_def, raisingMatrix, loweringMatrix, ← PEquiv.toMatrix_trans,
    ← PEquiv.toMatrix_trans]
  have hcomp :
      (T.raisingPEquiv i).symm.trans (T.raisingPEquiv j) =
        (T.raisingPEquiv j).trans (T.raisingPEquiv i).symm := by
    apply PEquiv.ext
    intro a
    exact T.raisingTarget_bind_loweringTarget_of_ne j i hij.symm a
  rw [hcomp, sub_self]

private theorem lie_raisingMatrix_loweringMatrix_self (i : B) :
    ⁅T.raisingMatrix i, T.loweringMatrix i⁆ = T.cartanGeneratorMatrix i := by
  ext a b
  simp only [Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply, T.raisingMatrix_apply,
    T.loweringMatrix_apply, mul_ite, mul_one, mul_zero, cartanGeneratorMatrix,
    Matrix.diagonal_apply]
  rcases T.weight_eq_neg_one_or_eq_zero_or_eq_one b i with h | h | h
  all_goals simp [h, T.weight_reflection_self, T.reflection_apply_apply]
  all_goals by_cases hab : a = b <;> simp_all

private theorem lie_cartanGeneratorMatrix_eq_smul_of_apply (i j : B) (M : Matrix ι ι ℤ) (s : ℤ)
    (hM : ∀ a b, M a b = if T.weight b j = s ∧ a = T.reflection j b then 1 else 0) :
    ⁅T.cartanGeneratorMatrix i, M⁆ = (-s * T.cartanMatrix i j) • M := by
  ext a b
  rw [cartanGeneratorMatrix]
  rw [TauCeti.lie_apply_of_mem_diagonalCartan
    (TauCeti.diagonal_mem_diagonalCartan (fun b ↦ T.weight b i))]
  rw [hM a b, Matrix.smul_apply, hM a b]
  simp only [Matrix.diagonal_apply_eq]
  split_ifs with h
  · obtain ⟨hb, rfl⟩ := h
    rw [T.weight_reflection, hb, T.cartanMatrix_comm]
    simp
  · simp

private theorem lie_cartanGeneratorMatrix_raisingMatrix (i j : B) :
    ⁅T.cartanGeneratorMatrix i, T.raisingMatrix j⁆ = T.cartanMatrix i j • T.raisingMatrix j := by
  simpa using T.lie_cartanGeneratorMatrix_eq_smul_of_apply i j (T.raisingMatrix j) (-1)
    (T.raisingMatrix_apply j)

private theorem lie_cartanGeneratorMatrix_loweringMatrix (i j : B) :
    ⁅T.cartanGeneratorMatrix i, T.loweringMatrix j⁆ =
      -(T.cartanMatrix i j • T.loweringMatrix j) := by
  simpa using T.lie_cartanGeneratorMatrix_eq_smul_of_apply i j (T.loweringMatrix j) 1
    (T.loweringMatrix_apply j)

omit [Fintype ι] in
private theorem cartanGeneratorMatrix_ne_zero (i : B) : T.cartanGeneratorMatrix i ≠ 0 := by
  intro hzero
  obtain ⟨a, ha⟩ := T.exists_weight_eq_neg_one i
  have h := congrFun (congrFun hzero a) a
  simp only [T.cartanGeneratorMatrix_apply, ite_true, Matrix.zero_apply] at h
  omega

/-- At each node, the three integral matrices of the table form an `sl₂` triple. -/
theorem isSl2Triple (i : B) :
    _root_.IsSl2Triple (T.cartanGeneratorMatrix i) (T.raisingMatrix i) (T.loweringMatrix i) where
  h_ne_zero := T.cartanGeneratorMatrix_ne_zero i
  lie_e_f := T.lie_raisingMatrix_loweringMatrix_self i
  lie_h_e_nsmul := by
    rw [T.lie_cartanGeneratorMatrix_raisingMatrix, T.cartanMatrix_self]
    simp
  lie_h_f_nsmul := by
    rw [T.lie_cartanGeneratorMatrix_loweringMatrix, T.cartanMatrix_self]
    simp

/-- **The integral matrices of a minuscule weight table satisfy the Serre relations of its Cartan
matrix.** -/
theorem isSerreSystem :
    TauCeti.IsSerreSystem ℤ T.cartanMatrix T.cartanGeneratorMatrix T.raisingMatrix
      T.loweringMatrix where
  lie_H_H := fun _ _ ↦ (Matrix.commute_diagonal _ _).lie_eq
  lie_E_F_self := T.lie_raisingMatrix_loweringMatrix_self
  lie_E_F_of_ne := T.lie_raisingMatrix_loweringMatrix_of_ne
  lie_H_E := T.lie_cartanGeneratorMatrix_raisingMatrix
  lie_H_F := T.lie_cartanGeneratorMatrix_loweringMatrix
  ad_pow_lie_E_E i j := by
    rcases eq_or_ne i j with rfl | hij
    · simp
    · exact TauCeti.ad_pow_lie_eq_zero_of_isSl2Triple_of_lie_h_eq_smul_of_lie_f_eq_zero
        (T.isSl2Triple i) (T.lie_cartanGeneratorMatrix_raisingMatrix i j)
        (by rw [← lie_skew, T.lie_raisingMatrix_loweringMatrix_of_ne j i hij.symm, neg_zero])
  ad_pow_lie_F_F i j := by
    rcases eq_or_ne i j with rfl | hij
    · simp
    · exact TauCeti.ad_pow_lie_eq_zero_of_isSl2Triple_of_lie_h_eq_smul_of_lie_f_eq_zero
        (T.isSl2Triple i).symm
        (by
          rw [neg_lie, T.lie_cartanGeneratorMatrix_loweringMatrix i j, neg_neg]
          simp only [Int.cast_id])
        (T.lie_raisingMatrix_loweringMatrix_of_ne i j hij)

variable [DecidableEq B]

/-- The integral representation of the Serre presentation named by a minuscule weight table. -/
noncomputable def serreRepresentation :
    Matrix.ToLieAlgebra ℤ T.cartanMatrix →ₗ⁅ℤ⁆ Matrix ι ι ℤ :=
  TauCeti.serreLift T.isSerreSystem

/-- The representation sends a Cartan generator to its diagonal weight matrix. -/
@[simp]
theorem serreRepresentation_serreH (i : B) :
    T.serreRepresentation (TauCeti.serreH ℤ T.cartanMatrix i) = T.cartanGeneratorMatrix i :=
  TauCeti.serreLift_serreH T.isSerreSystem i

/-- The representation sends a positive generator to its raising matrix. -/
@[simp]
theorem serreRepresentation_serreE (i : B) :
    T.serreRepresentation (TauCeti.serreE ℤ T.cartanMatrix i) = T.raisingMatrix i :=
  TauCeti.serreLift_serreE T.isSerreSystem i

/-- The representation sends a negative generator to its lowering matrix. -/
@[simp]
theorem serreRepresentation_serreF (i : B) :
    T.serreRepresentation (TauCeti.serreF ℤ T.cartanMatrix i) = T.loweringMatrix i :=
  TauCeti.serreLift_serreF T.isSerreSystem i

end MinusculeWeightTable

end TauCeti
