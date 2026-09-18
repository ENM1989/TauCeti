/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Frobenius on tensor products

The tensor product of Frobenius endomorphisms agrees with Frobenius on the tensor product when
the rings have the expected characteristic. This identity makes prime-field Frobenius commute
with bialgebra comultiplication, allowing the algebra endomorphism to be promoted to a bialgebra
endomorphism.
-/

public section

open scoped TensorProduct

namespace TauCeti

variable (p : ℕ) [Fact p.Prime] (S T : Type*) [CommRing S] [CommRing T]
  [Algebra (ZMod p) S] [Algebra (ZMod p) T]

/-- The tensor product of the `n`th Frobenius iterates is the `p ^ n`-power map of the tensor
product. -/
@[simp]
theorem tensorProductMap_frobeniusAlgHom_pow_apply (n : ℕ) (z : S ⊗[ZMod p] T) :
    Algebra.TensorProduct.map ((FiniteField.frobeniusAlgHom (ZMod p) S) ^ n)
        ((FiniteField.frobeniusAlgHom (ZMod p) T) ^ n) z =
      z ^ p ^ n := by
  have hmap :
      Algebra.TensorProduct.map ((FiniteField.frobeniusAlgHom (ZMod p) S) ^ n)
          ((FiniteField.frobeniusAlgHom (ZMod p) T) ^ n) =
        (FiniteField.frobeniusAlgHom (ZMod p) (S ⊗[ZMod p] T)) ^ n := by
    apply Algebra.TensorProduct.ext'
    intro a b
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.coe_pow,
      FiniteField.coe_frobeniusAlgHom, ZMod.card, pow_iterate,
      Algebra.TensorProduct.tmul_pow]
  rw [hmap]
  simp only [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, ZMod.card, pow_iterate]

end TauCeti
