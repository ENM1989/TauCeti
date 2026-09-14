/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Presentation.Serre
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.D.TripledWeight
public import Mathlib.Algebra.Lie.Sl2

import TauCeti.Algebra.Lie.GeneralLinear.DiagonalCartan
import TauCeti.Algebra.Lie.Sl2.WeightString
import Mathlib.Data.Matrix.PEquiv

/-!
# The tripled representation `V(ϖ₁) ⊕ V(ϖ₃) ⊕ V(ϖ₄)` of the type-D4 Serre presentation

This file constructs a `24`-dimensional integral representation of the type-`D₄` Serre
presentation, the direct sum of the natural representation and the two half-spin representations.
All three are minuscule, so the coordinate basis is indexed by their twenty-four weights, the
table `TauCeti.DynkinType.d4TripledWeight`.

For a simple root `i`, the raising matrix sends the basis vector of weight `μ` to the basis vector
of weight `μ + αᵢ` when `⟨μ, αᵢ∨⟩ = -1`, and to zero otherwise. The lowering matrix is defined
dually. The Cartan generator acts diagonally by the simple-coroot coordinate of the weight. Every
nonzero entry of a raising or lowering matrix is `1`, and the diagonal entries of the Cartan
generators are the weight coordinates, in `{-1, 0, 1}`: on a minuscule weight table no sign is
needed, which is what makes the triality symmetry of the table an unsigned symmetry of this
representation, recorded entrywise in `raisingMatrix_trialityPerm`,
`loweringMatrix_trialityPerm` and `cartanGeneratorMatrix_trialityPerm`. These integral matrices
satisfy the Serre relations for the type-`D₄` Cartan matrix. Identifying this
presentation with the split semisimple Lie algebra of type `D₄`, and hence interpreting these
matrices as a representation of that algebra, remains downstream.

This is the representation-theoretic input for the tripled type-`D₄` Chevalley carrier, a
full-weight carrier stable under triality. The weights span the full character lattice
by `TauCeti.DynkinType.span_range_d4TripledWeight_eq_top`; constructing the associated Kostant
carrier, its group scheme and its triality automorphism remains downstream.

## Main declarations

* `TauCeti.D4Tripled.raisingMatrix`, `loweringMatrix`, and `cartanGeneratorMatrix`: the integral
  Chevalley generators on the tripled weight basis.
* `TauCeti.D4Tripled.raisingMatrix_trialityPerm`, `loweringMatrix_trialityPerm`, and
  `cartanGeneratorMatrix_trialityPerm`: triality carries each generator at node `i` to the
  generator at node `trialityPermD4 i`, entrywise along `d4TripledTrialityPerm`.
* `TauCeti.D4Tripled.isSerreSystem`: the generators satisfy the type-`D₄` Serre relations.
* `TauCeti.D4Tripled.serreRepresentation`: the induced homomorphism from the integral type-`D₄`
  Serre presentation.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§13.4 and 27.
* R. W. Carter, *Simple Groups of Lie Type*, §12.2.
* The construction follows the formal template of `TauCeti.Algebra.Lie.E6.Minuscule.Basic`,
  specialized to the tripled weight table of type `D₄`.
-/

public section

open scoped Matrix

namespace TauCeti.D4Tripled

open TauCeti.DynkinType

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The target of the `i`-th raising operator on a tripled weight-basis vector, when nonzero. -/
private def raisingTarget (i : Fin 4) (a : Fin 24) : Option (Fin 24) :=
  if d4TripledWeight a i = -1 then some (d4TripledReflection i a) else none

/-- The target of the `i`-th lowering operator on a tripled weight-basis vector, when nonzero. -/
private def loweringTarget (i : Fin 4) (a : Fin 24) : Option (Fin 24) :=
  if d4TripledWeight a i = 1 then some (d4TripledReflection i a) else none

/-- Simple reflection restricted to the weights on which the raising operator is nonzero. -/
private def raisingPEquiv (i : Fin 4) : Fin 24 ≃. Fin 24 where
  toFun := raisingTarget i
  invFun := loweringTarget i
  inv a b := by
    have h :
        (d4TripledWeight b i = 1 ∧ d4TripledReflection i b = a) ↔
          (d4TripledWeight a i = -1 ∧ d4TripledReflection i a = b) := by
      constructor
      · rintro ⟨hb, rfl⟩
        constructor
        · rw [d4TripledWeight_reflection_apply_self]
          omega
        · exact d4TripledReflection_apply_apply i b
      · rintro ⟨ha, rfl⟩
        constructor
        · rw [d4TripledWeight_reflection_apply_self]
          omega
        · exact d4TripledReflection_apply_apply i a
    simpa [raisingTarget, loweringTarget] using h

/-- The raising matrix of the `i`-th simple root on the integral tripled weight basis. -/
def raisingMatrix (i : Fin 4) : Matrix (Fin 24) (Fin 24) ℤ :=
  (raisingPEquiv i).symm.toMatrix

/-- The lowering matrix of the `i`-th simple root on the integral tripled weight basis. -/
def loweringMatrix (i : Fin 4) : Matrix (Fin 24) (Fin 24) ℤ :=
  (raisingPEquiv i).toMatrix

/-- The diagonal matrix of the `i`-th simple coroot on the integral tripled weight basis. -/
def cartanGeneratorMatrix (i : Fin 4) : Matrix (Fin 24) (Fin 24) ℤ :=
  Matrix.diagonal (fun b ↦ d4TripledWeight b i)

private theorem pEquivMatrix_apply (e : Fin 24 ≃. Fin 24) (a b : Fin 24) (p : Prop)
    [Decidable p] (h : b ∈ e a ↔ p) :
    (e.toMatrix : Matrix (Fin 24) (Fin 24) ℤ) a b = if p then 1 else 0 := by
  simp only [PEquiv.toMatrix_apply]
  exact if_congr h rfl rfl

/-- The entry formula for a simple raising matrix. -/
@[simp]
theorem raisingMatrix_apply (i : Fin 4) (a b : Fin 24) :
    raisingMatrix i a b =
      if d4TripledWeight b i = -1 ∧ a = d4TripledReflection i b then 1 else 0 := by
  rw [raisingMatrix]
  apply pEquivMatrix_apply
  rw [PEquiv.mem_iff_mem]
  simp [raisingPEquiv, raisingTarget, eq_comm]

/-- The entry formula for a simple lowering matrix. -/
@[simp]
theorem loweringMatrix_apply (i : Fin 4) (a b : Fin 24) :
    loweringMatrix i a b =
      if d4TripledWeight b i = 1 ∧ a = d4TripledReflection i b then 1 else 0 := by
  rw [loweringMatrix]
  apply pEquivMatrix_apply
  rw [← PEquiv.mem_iff_mem]
  simp only [raisingPEquiv, PEquiv.symm]
  simp [loweringTarget, eq_comm]

/-- The entry formula for a simple Cartan generator matrix. -/
@[simp]
theorem cartanGeneratorMatrix_apply (i : Fin 4) (a b : Fin 24) :
    cartanGeneratorMatrix i a b = if a = b then d4TripledWeight b i else 0 := by
  rw [cartanGeneratorMatrix, Matrix.diagonal_apply]
  split_ifs with h
  · subst b
    rfl
  · rfl

/-! ## Triality on the generators

Triality permutes the weight basis by `d4TripledTrialityPerm` and the nodes by `trialityPermD4`,
and it carries each Chevalley generator at a node to the generator at the image node, with no
change of sign: reading a generator at the image node in the image basis gives back the generator
at the original node.

None of the three equations is a `simp` lemma: the entry formulas `raisingMatrix_apply`,
`loweringMatrix_apply` and `cartanGeneratorMatrix_apply` are, and they already rewrite both sides
to conditions on the weight table, so the left-hand sides below are not `simp`-normal. -/

/-- Triality carries the raising matrix at node `i` to the raising matrix at node
`trialityPermD4 i`, entrywise along `d4TripledTrialityPerm`. -/
theorem raisingMatrix_trialityPerm (i : Fin 4) (a b : Fin 24) :
    raisingMatrix (trialityPermD4 i) (d4TripledTrialityPerm a) (d4TripledTrialityPerm b) =
      raisingMatrix i a b := by
  rw [raisingMatrix_apply, raisingMatrix_apply]
  simp only [d4TripledWeight_d4TripledTrialityPerm, ← d4TripledTrialityPerm_d4TripledReflection,
    Equiv.apply_eq_iff_eq]

/-- Triality carries the lowering matrix at node `i` to the lowering matrix at node
`trialityPermD4 i`, entrywise along `d4TripledTrialityPerm`. -/
theorem loweringMatrix_trialityPerm (i : Fin 4) (a b : Fin 24) :
    loweringMatrix (trialityPermD4 i) (d4TripledTrialityPerm a) (d4TripledTrialityPerm b) =
      loweringMatrix i a b := by
  rw [loweringMatrix_apply, loweringMatrix_apply]
  simp only [d4TripledWeight_d4TripledTrialityPerm, ← d4TripledTrialityPerm_d4TripledReflection,
    Equiv.apply_eq_iff_eq]

/-- Triality carries the Cartan generator at node `i` to the Cartan generator at node
`trialityPermD4 i`, entrywise along `d4TripledTrialityPerm`. -/
theorem cartanGeneratorMatrix_trialityPerm (i : Fin 4) (a b : Fin 24) :
    cartanGeneratorMatrix (trialityPermD4 i) (d4TripledTrialityPerm a) (d4TripledTrialityPerm b) =
      cartanGeneratorMatrix i a b := by
  rw [cartanGeneratorMatrix_apply, cartanGeneratorMatrix_apply]
  simp only [d4TripledWeight_d4TripledTrialityPerm, Equiv.apply_eq_iff_eq]

private theorem cartanMatrix_D_symmetric (i j : Fin 4) :
    CartanMatrix.D 4 j i = CartanMatrix.D 4 i j :=
  (CartanMatrix.D_isSymm 4).apply i j

@[simp]
private theorem raisingTarget_eq_some_iff (i : Fin 4) (a b : Fin 24) :
    raisingTarget i a = some b ↔
      d4TripledWeight a i = -1 ∧ b = d4TripledReflection i a := by
  simp [raisingTarget, eq_comm]

@[simp]
private theorem loweringTarget_eq_some_iff (i : Fin 4) (a b : Fin 24) :
    loweringTarget i a = some b ↔
      d4TripledWeight a i = 1 ∧ b = d4TripledReflection i a := by
  simp [loweringTarget, eq_comm]

private theorem d4TripledWeight_reflection_apply_of_cartan_eq_zero (i j : Fin 4)
    (a : Fin 24) (hij : CartanMatrix.D 4 i j = 0) :
    d4TripledWeight (d4TripledReflection i a) j = d4TripledWeight a j := by
  rw [d4TripledWeight_reflection_apply, hij]
  ring

private theorem raisingTarget_bind_loweringTarget_of_cartan_eq_zero (i j : Fin 4)
    (hij : CartanMatrix.D 4 i j = 0) (a : Fin 24) :
    (loweringTarget j a).bind (raisingTarget i) =
      (raisingTarget i a).bind (loweringTarget j) := by
  have hji : CartanMatrix.D 4 j i = 0 := by
    rw [cartanMatrix_D_symmetric i j, hij]
  by_cases hi : d4TripledWeight a i = -1
  · by_cases hj : d4TripledWeight a j = 1
    · simp [raisingTarget, loweringTarget, hi, hj,
        d4TripledWeight_reflection_apply_of_cartan_eq_zero i j a hij,
        d4TripledWeight_reflection_apply_of_cartan_eq_zero j i a hji,
        d4TripledReflection_comm_of_cartan_eq_zero i j a hij]
    · simp [raisingTarget, loweringTarget, hi, hj,
        d4TripledWeight_reflection_apply_of_cartan_eq_zero i j a hij]
  · by_cases hj : d4TripledWeight a j = 1
    · simp [raisingTarget, loweringTarget, hi, hj,
        d4TripledWeight_reflection_apply_of_cartan_eq_zero j i a hji]
    · simp [raisingTarget, loweringTarget, hi, hj]

private theorem raisingTarget_bind_loweringTarget_of_cartan_eq_neg_one (i j : Fin 4)
    (hij : CartanMatrix.D 4 i j = -1) (a : Fin 24) :
    (loweringTarget j a).bind (raisingTarget i) =
      (raisingTarget i a).bind (loweringTarget j) := by
  have hi_lower : -1 ≤ d4TripledWeight a i := by
    rcases d4TripledWeight_apply_eq_neg_one_or_eq_zero_or_eq_one a i with hi | hi | hi <;>
      omega
  have hj_upper : d4TripledWeight a j ≤ 1 := by
    rcases d4TripledWeight_apply_eq_neg_one_or_eq_zero_or_eq_one a j with hj | hj | hj <;>
      omega
  have hji : CartanMatrix.D 4 j i = -1 := by
    rw [cartanMatrix_D_symmetric i j, hij]
  have hleft : (loweringTarget j a).bind (raisingTarget i) = none := by
    by_cases hj : d4TripledWeight a j = 1
    · have href : d4TripledWeight (d4TripledReflection j a) i ≠ -1 := by
        rw [d4TripledWeight_reflection_apply, hj, hji]
        omega
      simp [loweringTarget, raisingTarget, hj, href]
    · simp [loweringTarget, hj]
  have hright : (raisingTarget i a).bind (loweringTarget j) = none := by
    by_cases hi : d4TripledWeight a i = -1
    · have href : d4TripledWeight (d4TripledReflection i a) j ≠ 1 := by
        rw [d4TripledWeight_reflection_apply, hi, hij]
        omega
      simp [raisingTarget, loweringTarget, hi, href]
    · simp [raisingTarget, hi]
  rw [hleft, hright]

private theorem raisingTarget_bind_loweringTarget_of_ne (i j : Fin 4) (hij : i ≠ j)
    (a : Fin 24) :
    (loweringTarget j a).bind (raisingTarget i) =
      (raisingTarget i a).bind (loweringTarget j) := by
  rcases CartanMatrix.isSimplyLaced_D 4 hij with hA | hA
  · exact raisingTarget_bind_loweringTarget_of_cartan_eq_zero i j hA a
  · exact raisingTarget_bind_loweringTarget_of_cartan_eq_neg_one i j hA a

private theorem lie_raisingMatrix_loweringMatrix_of_ne (i j : Fin 4) (hij : i ≠ j) :
    ⁅raisingMatrix i, loweringMatrix j⁆ = 0 := by
  rw [Ring.lie_def, raisingMatrix, loweringMatrix, ← PEquiv.toMatrix_trans,
    ← PEquiv.toMatrix_trans]
  have hcomp :
      (raisingPEquiv i).symm.trans (raisingPEquiv j) =
        (raisingPEquiv j).trans (raisingPEquiv i).symm := by
    apply PEquiv.ext
    intro a
    exact raisingTarget_bind_loweringTarget_of_ne j i hij.symm a
  rw [hcomp, sub_self]

private theorem lie_raisingMatrix_loweringMatrix_self (i : Fin 4) :
    ⁅raisingMatrix i, loweringMatrix i⁆ = cartanGeneratorMatrix i := by
  ext a b
  simp only [Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply, raisingMatrix_apply,
    loweringMatrix_apply, mul_ite, mul_one, mul_zero, cartanGeneratorMatrix,
    Matrix.diagonal_apply]
  rcases d4TripledWeight_apply_eq_neg_one_or_eq_zero_or_eq_one b i with h | h | h
  all_goals simp [h, d4TripledWeight_reflection_apply_self, d4TripledReflection_apply_apply]
  all_goals by_cases hab : a = b <;> simp_all

private theorem lie_cartanGeneratorMatrix_eq_smul_of_apply (i j : Fin 4)
    (M : Matrix (Fin 24) (Fin 24) ℤ) (s : ℤ)
    (hM : ∀ a b, M a b =
      if d4TripledWeight b j = s ∧ a = d4TripledReflection j b then 1 else 0) :
    ⁅cartanGeneratorMatrix i, M⁆ = (-s * CartanMatrix.D 4 i j) • M := by
  ext a b
  rw [cartanGeneratorMatrix]
  rw [TauCeti.lie_apply_of_mem_diagonalCartan
    (TauCeti.diagonal_mem_diagonalCartan (fun b ↦ d4TripledWeight b i))]
  rw [hM a b, Matrix.smul_apply, hM a b]
  simp only [Matrix.diagonal_apply_eq]
  split_ifs with h
  · obtain ⟨hb, rfl⟩ := h
    rw [d4TripledWeight_reflection_apply, hb, cartanMatrix_D_symmetric]
    simp
  · simp

private theorem lie_cartanGeneratorMatrix_raisingMatrix (i j : Fin 4) :
    ⁅cartanGeneratorMatrix i, raisingMatrix j⁆ = CartanMatrix.D 4 i j • raisingMatrix j := by
  simpa using lie_cartanGeneratorMatrix_eq_smul_of_apply i j (raisingMatrix j) (-1)
    (raisingMatrix_apply j)

private theorem lie_cartanGeneratorMatrix_loweringMatrix (i j : Fin 4) :
    ⁅cartanGeneratorMatrix i, loweringMatrix j⁆ =
      -(CartanMatrix.D 4 i j • loweringMatrix j) := by
  simpa using lie_cartanGeneratorMatrix_eq_smul_of_apply i j (loweringMatrix j) 1
    (loweringMatrix_apply j)

private theorem cartanGeneratorMatrix_ne_zero (i : Fin 4) : cartanGeneratorMatrix i ≠ 0 := by
  intro hzero
  obtain ⟨a, ha⟩ := exists_d4TripledWeight_apply_eq_neg_one i
  have h := congrFun (congrFun hzero a) a
  simp only [cartanGeneratorMatrix_apply, ite_true, Matrix.zero_apply] at h
  omega

/-- At each simple node, the three integral tripled matrices form an `sl₂` triple. -/
theorem isSl2Triple (i : Fin 4) :
    _root_.IsSl2Triple (cartanGeneratorMatrix i) (raisingMatrix i) (loweringMatrix i) where
  h_ne_zero := cartanGeneratorMatrix_ne_zero i
  lie_e_f := lie_raisingMatrix_loweringMatrix_self i
  lie_h_e_nsmul := by
    rw [lie_cartanGeneratorMatrix_raisingMatrix, CartanMatrix.D_diag]
    simp
  lie_h_f_nsmul := by
    rw [lie_cartanGeneratorMatrix_loweringMatrix, CartanMatrix.D_diag]
    simp

/-- **The integral `24`-dimensional tripled matrices satisfy the Serre relations of type
`D₄`.** The type-`D₄` Cartan matrix is symmetric, so no transpose is needed to place the coroot
index first. -/
theorem isSerreSystem :
    TauCeti.IsSerreSystem ℤ (CartanMatrix.D 4) cartanGeneratorMatrix raisingMatrix
      loweringMatrix where
  lie_H_H := fun _ _ ↦ (Matrix.commute_diagonal _ _).lie_eq
  lie_E_F_self := lie_raisingMatrix_loweringMatrix_self
  lie_E_F_of_ne := lie_raisingMatrix_loweringMatrix_of_ne
  lie_H_E := lie_cartanGeneratorMatrix_raisingMatrix
  lie_H_F := lie_cartanGeneratorMatrix_loweringMatrix
  ad_pow_lie_E_E i j := by
    rcases eq_or_ne i j with rfl | hij
    · simp
    · exact TauCeti.ad_pow_lie_eq_zero_of_isSl2Triple_of_lie_h_eq_smul_of_lie_f_eq_zero
        (isSl2Triple i) (lie_cartanGeneratorMatrix_raisingMatrix i j)
        (by rw [← lie_skew, lie_raisingMatrix_loweringMatrix_of_ne j i hij.symm, neg_zero])
  ad_pow_lie_F_F i j := by
    rcases eq_or_ne i j with rfl | hij
    · simp
    · exact TauCeti.ad_pow_lie_eq_zero_of_isSl2Triple_of_lie_h_eq_smul_of_lie_f_eq_zero
        (isSl2Triple i).symm
        (by
          rw [neg_lie, lie_cartanGeneratorMatrix_loweringMatrix i j, neg_neg]
          simp only [Int.cast_id])
        (lie_raisingMatrix_loweringMatrix_of_ne i j hij)

/-- The integral `24`-dimensional tripled representation of the type-`D₄` Serre presentation. -/
noncomputable def serreRepresentation :
    Matrix.ToLieAlgebra ℤ (CartanMatrix.D 4) →ₗ⁅ℤ⁆ Matrix (Fin 24) (Fin 24) ℤ :=
  TauCeti.serreLift isSerreSystem

/-- The tripled representation sends a Cartan generator to its diagonal weight matrix. -/
@[simp]
theorem serreRepresentation_serreH (i : Fin 4) :
    serreRepresentation (TauCeti.serreH ℤ (CartanMatrix.D 4) i) = cartanGeneratorMatrix i :=
  TauCeti.serreLift_serreH isSerreSystem i

/-- The tripled representation sends a positive generator to its raising matrix. -/
@[simp]
theorem serreRepresentation_serreE (i : Fin 4) :
    serreRepresentation (TauCeti.serreE ℤ (CartanMatrix.D 4) i) = raisingMatrix i :=
  TauCeti.serreLift_serreE isSerreSystem i

/-- The tripled representation sends a negative generator to its lowering matrix. -/
@[simp]
theorem serreRepresentation_serreF (i : Fin 4) :
    serreRepresentation (TauCeti.serreF ℤ (CartanMatrix.D 4) i) = loweringMatrix i :=
  TauCeti.serreLift_serreF isSerreSystem i

end TauCeti.D4Tripled
