/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Nilpotent.BaseChangeAction
public import Mathlib.Algebra.Lie.Derivation.BaseChange

/-!
# Integral exponentials of nilpotent Lie derivations

Let `D` be a nilpotent derivation of a Lie algebra over `ℚ`, and let an integral Lie subalgebra be
stable under every divided power `Dⁿ / n!`. The restricted divided powers obey the coefficient-free
Leibniz rule. Consequently their finite exponential preserves the Lie bracket after scalar
extension to an arbitrary commutative ring, even when factorials are not invertible in that ring.

## Main declarations

* `TauCeti.LieDerivation.dividedPower_apply_lie`: coefficient-free divided-power Leibniz rule.
* `TauCeti.integralDividedPower_lie`: the rule on the integral Lie subalgebra.
* `TauCeti.baseChangeExp_lie`: bracket preservation after arbitrary base change.
* `TauCeti.baseChangeExpLieEquiv`: the resulting Lie algebra automorphism.
-/

public section

namespace TauCeti

open Finset TensorProduct

universe u v

noncomputable section

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]

/-- Divided powers of a Lie derivation satisfy the coefficient-free divided-power Leibniz rule. -/
theorem LieDerivation.dividedPower_apply_lie (D : LieDerivation ℚ L L) (n : ℕ) (x y : L) :
    Associative.dividedPower n D.toLinearMap ⁅x, y⁆ =
      ∑ ij ∈ antidiagonal n,
        ⁅Associative.dividedPower ij.1 D.toLinearMap x,
          Associative.dividedPower ij.2 D.toLinearMap y⁆ := by
  rw [Associative.dividedPower_def, LinearMap.smul_apply, Module.End.pow_apply,
    show (⇑D.toLinearMap)^[n] ⁅x, y⁆ = D^[n] ⁅x, y⁆ from rfl,
    LieDerivation.iterate_apply_lie]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun ij hij => ?_
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
  simp only [Associative.dividedPower_def, LinearMap.smul_apply, Module.End.pow_apply,
    lie_smul, smul_lie, smul_smul]
  rw [mem_antidiagonal] at hij
  subst n
  change
    ((↑(ij.1 + ij.2).factorial : ℚ)⁻¹ * ↑((ij.1 + ij.2).choose ij.1)) •
        ⁅D^[ij.1] x, D^[ij.2] y⁆ =
      ((↑ij.2.factorial : ℚ)⁻¹ * (↑ij.1.factorial : ℚ)⁻¹) •
        ⁅D^[ij.1] x, D^[ij.2] y⁆
  congr 1
  field_simp
  exact_mod_cast (by
    simpa [Nat.add_comm] using Nat.add_choose_mul_factorial_mul_factorial ij.2 ij.1)

/-- Restricted integral divided powers inherit the coefficient-free Leibniz rule. -/
theorem integralDividedPower_lie (D : LieDerivation ℚ L L) (M : LieSubalgebra ℤ L)
    (hM : ∀ n, ∀ x ∈ M, Associative.dividedPower n D.toLinearMap x ∈ M)
    (n : ℕ) (x y : M) :
    integralDividedPower D.toLinearMap M n (hM n) ⁅x, y⁆ =
      ∑ ij ∈ antidiagonal n,
        ⁅integralDividedPower D.toLinearMap M ij.1 (hM ij.1) x,
          integralDividedPower D.toLinearMap M ij.2 (hM ij.2) y⁆ := by
  apply SetLike.coe_eq_coe.mp
  rw [coe_integralDividedPower_apply]
  simp only [LieSubalgebra.coe_bracket, AddSubmonoidClass.coe_finsetSum]
  change Associative.dividedPower n D.toLinearMap ⁅(x : L), (y : L)⁆ = _
  rw [TauCeti.LieDerivation.dividedPower_apply_lie]
  exact Finset.sum_congr rfl fun ij _ => by
    rw [coe_integralDividedPower_apply, coe_integralDividedPower_apply]
    rfl

private theorem sum_range_two_mul_antidiagonal_of_support
    {N : Type*} [AddCommMonoid N] (k : ℕ) (f : ℕ × ℕ → N)
    (hf : ∀ i j, k ≤ i ∨ k ≤ j → f (i, j) = 0) :
    ∑ n ∈ range (2 * k), ∑ ij ∈ antidiagonal n, f ij =
      ∑ i ∈ range k, ∑ j ∈ range k, f (i, j) := by
  classical
  let s := (range (2 * k)).sigma fun n => antidiagonal n
  let t := s.filter fun q => q.2.1 < k ∧ q.2.2 < k
  rw [Finset.sum_sigma']
  change (∑ q ∈ s, f q.2) = _
  have hfilter : (∑ q ∈ t, f q.2) = ∑ q ∈ s, f q.2 := by
    apply Finset.sum_subset (by simp [t])
    intro q hqs hqt
    rw [Finset.mem_filter] at hqt
    simp only [hqs, true_and, not_and_or, not_lt] at hqt
    exact hf q.2.1 q.2.2 hqt
  rw [← hfilter, ← Finset.sum_product']
  apply Finset.sum_bij (fun q _ => q.2)
  · intro q hq
    rw [Finset.mem_filter] at hq
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact hq.2
  · intro q₁ hq₁ q₂ hq₂ hqq
    rcases q₁ with ⟨n₁, ij₁⟩
    rcases q₂ with ⟨n₂, ij₂⟩
    dsimp only at hqq
    subst ij₂
    rw [Finset.mem_filter, Finset.mem_sigma, mem_antidiagonal] at hq₁ hq₂
    have hn : n₁ = n₂ := hq₁.1.2.symm.trans hq₂.1.2
    subst n₂
    rfl
  · intro ij hij
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hij
    let q : (n : ℕ) × (ℕ × ℕ) := ⟨ij.1 + ij.2, ij⟩
    have hsum : ij.1 + ij.2 < 2 * k := by omega
    have hq : q ∈ t := by
      rw [Finset.mem_filter, Finset.mem_sigma, Finset.mem_range, mem_antidiagonal]
      exact ⟨⟨hsum, rfl⟩, hij⟩
    exact ⟨q, hq, rfl⟩
  · intro q _
    rfl

variable {R : Type v} [CommRing R] [Algebra ℤ R]

attribute [local instance high] Algebra.toModule

/-- The integral divided-power exponential preserves the Lie bracket on pure tensors after an
arbitrary base change. -/
theorem baseChangeExp_tmul_lie (D : LieDerivation ℚ L L) (M : LieSubalgebra ℤ L)
    (hM : ∀ n, ∀ x ∈ M, Associative.dividedPower n D.toLinearMap x ∈ M)
    (hD : IsNilpotent D.toLinearMap) (t a b : R) (x y : M) :
    baseChangeExp D.toLinearMap M hM t
        ⁅a ⊗ₜ[ℤ] x, b ⊗ₜ[ℤ] y⁆ =
      ⁅baseChangeExp D.toLinearMap M hM t (a ⊗ₜ[ℤ] x),
        baseChangeExp D.toLinearMap M hM t (b ⊗ₜ[ℤ] y)⁆ := by
  obtain ⟨k, hk⟩ := hD
  have hk2 : D.toLinearMap ^ (2 * k) = 0 := by
    rw [show 2 * k = k + k by omega, pow_add, hk, zero_mul]
  let d := fun n => integralDividedPower D.toLinearMap M n (hM n)
  rw [LieAlgebra.ExtendScalars.bracket_tmul,
    baseChangeExp_tmul_of_pow_eq_zero D.toLinearMap M hM hk2,
    baseChangeExp_tmul_of_pow_eq_zero D.toLinearMap M hM hk2,
    baseChangeExp_tmul_of_pow_eq_zero D.toLinearMap M hM hk2]
  rw [sum_lie (range (2 * k))
    (fun n => (t ^ n * a) ⊗ₜ[ℤ] d n x)
    (∑ n ∈ range (2 * k), (t ^ n * b) ⊗ₜ[ℤ] d n y)]
  simp_rw [lie_sum, LieAlgebra.ExtendScalars.bracket_tmul]
  calc
    (∑ n ∈ range (2 * k), (t ^ n * (a * b)) ⊗ₜ[ℤ] d n ⁅x, y⁆) =
        ∑ n ∈ range (2 * k), ∑ ij ∈ antidiagonal n,
          (t ^ (ij.1 + ij.2) * (a * b)) ⊗ₜ[ℤ] ⁅d ij.1 x, d ij.2 y⁆ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [integralDividedPower_lie, TensorProduct.tmul_sum]
      apply Finset.sum_congr rfl
      intro ij hij
      rw [mem_antidiagonal] at hij
      rw [hij]
    _ = ∑ i ∈ range k, ∑ j ∈ range k,
          (t ^ (i + j) * (a * b)) ⊗ₜ[ℤ] ⁅d i x, d j y⁆ := by
      apply sum_range_two_mul_antidiagonal_of_support
      intro i j hij
      dsimp only [d]
      rcases hij with hi | hj
      · rw [integralDividedPower_eq_zero_of_le D.toLinearMap M i (hM i) hk hi,
          LinearMap.zero_apply, zero_lie, TensorProduct.tmul_zero]
      · rw [integralDividedPower_eq_zero_of_le D.toLinearMap M j (hM j) hk hj,
          LinearMap.zero_apply, lie_zero, TensorProduct.tmul_zero]
    _ = ∑ i ∈ range k, ∑ j ∈ range k,
          ((t ^ i * a) * (t ^ j * b)) ⊗ₜ[ℤ] ⁅d i x, d j y⁆ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      ring
    _ = ∑ i ∈ range (2 * k), ∑ j ∈ range (2 * k),
          ((t ^ i * a) * (t ^ j * b)) ⊗ₜ[ℤ] ⁅d i x, d j y⁆ := by
      rw [← Finset.sum_product', ← Finset.sum_product']
      apply Finset.sum_subset (product_subset_product (Finset.range_mono (by omega))
        (Finset.range_mono (by omega)))
      intro ij hij hnot
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hij
      by_cases hi : k ≤ ij.1
      · dsimp only [d]
        rw [integralDividedPower_eq_zero_of_le D.toLinearMap M ij.1 (hM ij.1) hk hi,
          LinearMap.zero_apply, zero_lie, TensorProduct.tmul_zero]
      · have hj : k ≤ ij.2 := by
          rw [Finset.mem_product, Finset.mem_range, Finset.mem_range, not_and_or, not_lt] at hnot
          exact not_lt.mp (hnot.resolve_left (not_le.2 (not_le.1 hi)))
        dsimp only [d]
        rw [integralDividedPower_eq_zero_of_le D.toLinearMap M ij.2 (hM ij.2) hk hj,
          LinearMap.zero_apply, lie_zero, TensorProduct.tmul_zero]

/-- The integral divided-power exponential preserves the Lie bracket after an arbitrary base
change. No finite-dimensionality, flatness, or characteristic assumption is needed on the new
base ring. -/
theorem baseChangeExp_lie (D : LieDerivation ℚ L L) (M : LieSubalgebra ℤ L)
    (hM : ∀ n, ∀ x ∈ M, Associative.dividedPower n D.toLinearMap x ∈ M)
    (hD : IsNilpotent D.toLinearMap) (t : R) (x y : R ⊗[ℤ] M) :
    baseChangeExp D.toLinearMap M hM t ⁅x, y⁆ =
      ⁅baseChangeExp D.toLinearMap M hM t x,
        baseChangeExp D.toLinearMap M hM t y⁆ := by
  let _ : LieRing (R ⊗[ℤ] M) := LieAlgebra.ExtendScalars.instLieRing ℤ R M
  let _ : LieAlgebra R (R ⊗[ℤ] M) := LieAlgebra.ExtendScalars.instLieAlgebra ℤ R M
  induction x using TensorProduct.induction_on with
  | zero => rw [zero_lie, map_zero, zero_lie]
  | tmul a x =>
      induction y using TensorProduct.induction_on with
      | zero => rw [lie_zero, map_zero, lie_zero]
      | tmul b y => exact baseChangeExp_tmul_lie D M hM hD t a b x y
      | add y z hy hz =>
          rw [lie_add, map_add, hy, hz]
          rw [map_add, lie_add]
  | add x z hx hz =>
      rw [add_lie, map_add, hx, hz]
      rw [map_add, add_lie]

/-- The integral divided-power exponential of a nilpotent Lie derivation, after arbitrary base
change, as a Lie algebra automorphism. -/
noncomputable def baseChangeExpLieEquiv (D : LieDerivation ℚ L L) (M : LieSubalgebra ℤ L)
    (hM : ∀ n, ∀ x ∈ M, Associative.dividedPower n D.toLinearMap x ∈ M)
    (hD : IsNilpotent D.toLinearMap) (t : R) :
    R ⊗[ℤ] M ≃ₗ⁅R⁆ R ⊗[ℤ] M :=
  { baseChangeExpLinearEquiv D.toLinearMap M hM hD t with
    map_lie' := by
      intro x y
      change (baseChangeExpLinearEquiv D.toLinearMap M hM hD t).toLinearMap ⁅x, y⁆ = _
      rw [baseChangeExpLinearEquiv_toLinearMap]
      exact baseChangeExp_lie D M hM hD t x y }

end

end TauCeti
