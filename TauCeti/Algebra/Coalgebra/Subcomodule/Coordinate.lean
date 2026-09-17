/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Matrix
public import TauCeti.Algebra.Coalgebra.Subcomodule.Basic
public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Coordinate subcomodules

A subset of a finite basis spans a subcomodule exactly when the corresponding columns of the
coefficient matrix have no entries outside that subset. This is a scheme-level criterion: it
uses the universal coaction and requires no separation hypothesis on algebra-valued points.

## Main declarations

* `TauCeti.Comodule.coordinateSpanIsStable`: the coefficient-vanishing condition for a basis
  subset.
* `TauCeti.Comodule.coordinateSpanSubcomodule`: the coordinate span as a subcomodule.
* `TauCeti.Comodule.exists_coordinateSpanSubcomodule_iff`: the coefficient criterion is also
  necessary.
* `TauCeti.Comodule.weightCoordinateSpanIsStable_iff_blockTriangular`: every upper weight
  filtration step is stable exactly when the coefficient matrix is block triangular by weight.
-/

public section

open Module
open scoped TensorProduct

namespace TauCeti.Comodule

universe u v w x

noncomputable section

variable {R : Type u} {C : Type v} {M : Type w} {ι : Type x}
variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]

/-- The coefficient-matrix condition saying that the span of the basis vectors indexed by `s`
is stable under the coaction. A column indexed by `j ∈ s` has no entry in a row outside `s`. -/
def coordinateSpanIsStable (b : Basis ι R M) (s : Set ι) : Prop :=
  ∀ i, i ∉ s → ∀ j, j ∈ s → coefficientMatrix (C := C) b i j = 0

/-- A basis subset whose coefficient columns have no entries outside the subset spans a
subcomodule. -/
@[expose] def coordinateSpanSubcomodule (b : Basis ι R M) (s : Set ι)
    [Fintype ι] (h : coordinateSpanIsStable (C := C) b s) : Subcomodule R C M :=
  Subcomodule.ofSubmodule (Submodule.span R (b '' s)) fun m hm => by
    classical
    let N := Submodule.span R (b '' s)
    have h' := h
    unfold coordinateSpanIsStable at h'
    induction hm using Submodule.span_induction with
    | mem m hm =>
        obtain ⟨j, hj, rfl⟩ := hm
        rw [coact_basis_eq_sum_coefficientMatrix]
        refine ⟨∑ i, if hi : i ∈ s then
            (⟨b i, Submodule.subset_span ⟨i, hi, rfl⟩⟩ : N) ⊗ₜ[R]
              coefficientMatrix (C := C) b i j else 0, ?_⟩
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i ∈ s
        · simp only [dite_eq_left hi, TensorProduct.map_tmul, Submodule.coe_subtype,
            LinearMap.id_apply]
        · rw [dite_eq_right hi, map_zero, h' i hi j hj, TensorProduct.tmul_zero]
    | zero =>
        rw [map_zero]
        exact (LinearMap.range (TensorProduct.map N.subtype
          (LinearMap.id : C →ₗ[R] C))).zero_mem
    | add x y _ _ hx hy =>
        rw [map_add]
        exact (LinearMap.range (TensorProduct.map N.subtype
          (LinearMap.id : C →ₗ[R] C))).add_mem hx hy
    | smul r x _ hx =>
        rw [map_smul]
        exact (LinearMap.range (TensorProduct.map N.subtype
          (LinearMap.id : C →ₗ[R] C))).smul_mem r hx

/-- The underlying submodule of a coordinate-span subcomodule is the span of the selected basis
vectors. -/
@[simp]
theorem coordinateSpanSubcomodule_toSubmodule (b : Basis ι R M) (s : Set ι)
    [Fintype ι] (h : coordinateSpanIsStable (C := C) b s) :
    (coordinateSpanSubcomodule b s h).toSubmodule = Submodule.span R (b '' s) :=
  rfl

/-- A basis subset spans a subcomodule if and only if its coefficient columns have no entries
outside the subset. -/
theorem exists_coordinateSpanSubcomodule_iff [Finite ι] (b : Basis ι R M) (s : Set ι) :
    (∃ N : Subcomodule R C M, N.toSubmodule = Submodule.span R (b '' s)) ↔
      coordinateSpanIsStable (C := C) b s := by
  let _ := Fintype.ofFinite ι
  constructor
  · rintro ⟨N, hN⟩
    unfold coordinateSpanIsStable
    intro i hi j hj
    have hbj : b j ∈ N := by
      rw [← Subcomodule.mem_toSubmodule, hN]
      exact Submodule.subset_span ⟨j, hj, rfl⟩
    obtain ⟨t, ht⟩ := N.coact_mem hbj
    rw [coefficientMatrix_apply, matrixCoefficient_def, ← ht]
    have hcoord : (b.coord i).comp N.carrier.subtype = 0 := by
      ext x
      rw [LinearMap.zero_apply]
      have hx : (x : M) ∈ Submodule.span R (b '' s) := hN ▸ x.2
      have hisupport : i ∉ (b.repr (x : M)).support := by
        intro his
        exact hi ((b.mem_span_image.mp hx) his)
      exact Finsupp.notMem_support_iff.mp hisupport
    rw [TensorProduct.map_map, LinearMap.id_comp, hcoord,
      TensorProduct.map_zero_left, LinearMap.zero_apply, map_zero]
  · intro h
    exact ⟨coordinateSpanSubcomodule b s h, coordinateSpanSubcomodule_toSubmodule b s h⟩

section WeightFiltration

variable {α : Type*} [LinearOrder α]

/-- Every upper weight-filtration step in a based comodule satisfies the coordinate-vanishing
criterion. -/
def weightCoordinateSpanIsStable (b : Basis ι R M) (weight : ι → α) : Prop :=
  ∀ r, coordinateSpanIsStable (C := C) b {i | r ≤ weight i}

/-- The upper weight-filtration steps are stable exactly when the coefficient matrix is block
triangular with respect to the opposite weight order. The opposite order records that a column
of weight `r` may only have rows of weight at least `r`. -/
theorem weightCoordinateSpanIsStable_iff_blockTriangular (b : Basis ι R M) (weight : ι → α) :
    weightCoordinateSpanIsStable (C := C) b weight ↔
      (coefficientMatrix (C := C) b).BlockTriangular (OrderDual.toDual ∘ weight) := by
  constructor
  · intro h i j hij
    unfold weightCoordinateSpanIsStable at h
    change weight i < weight j at hij
    have hs := h (weight j)
    unfold coordinateSpanIsStable at hs
    exact hs i (by simpa only [Set.mem_ofPred_eq] using (not_le_of_gt hij)) j (by simp)
  · intro h r
    unfold coordinateSpanIsStable
    intro i hi j hj
    apply h
    change weight i < weight j
    have hi' : ¬r ≤ weight i := by simpa only [Set.mem_ofPred_eq] using hi
    have hj' : r ≤ weight j := by simpa only [Set.mem_ofPred_eq] using hj
    exact lt_of_lt_of_le (lt_of_not_ge hi') hj'

/-- A block-triangular coefficient matrix makes each upper weight-filtration step a
subcomodule. -/
@[expose] def weightCoordinateSpanSubcomodule (b : Basis ι R M) (weight : ι → α) (r : α)
    [Fintype ι]
    (h : (coefficientMatrix (C := C) b).BlockTriangular (OrderDual.toDual ∘ weight)) :
    Subcomodule R C M :=
  coordinateSpanSubcomodule b {i | r ≤ weight i} (by
    have hs := (weightCoordinateSpanIsStable_iff_blockTriangular (C := C) b weight).mpr h
    unfold weightCoordinateSpanIsStable at hs
    exact hs r)

/-- The underlying submodule of an upper weight-filtration subcomodule is the span of the
basis vectors of weight at least the cutoff. -/
@[simp]
theorem weightCoordinateSpanSubcomodule_toSubmodule (b : Basis ι R M) (weight : ι → α) (r : α)
    [Fintype ι]
    (h : (coefficientMatrix (C := C) b).BlockTriangular (OrderDual.toDual ∘ weight)) :
    (weightCoordinateSpanSubcomodule b weight r h).toSubmodule =
      Submodule.span R (b '' {i | r ≤ weight i}) :=
  rfl

end WeightFiltration

end

end TauCeti.Comodule
