/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Basic
public import TauCeti.Algebra.CharP.Frobenius.PrimeField

/-!
# Frobenius on tensor squares

The tensor square of the Frobenius endomorphism agrees with Frobenius on the tensor square when
both rings have the expected characteristic.
-/

public section

open scoped TensorProduct

namespace TauCeti

variable (p : ℕ) [Fact p.Prime] (S : Type*) [CommRing S] [Algebra (ZMod p) S]
  [CharP S p] [CharP (S ⊗[ZMod p] S) p]

/-- The tensor square of the `p`-power map is the `p`-power map of the tensor square. -/
theorem map_iterateFrobeniusAlgHom_tensorSquare (z : S ⊗[ZMod p] S) :
    Algebra.TensorProduct.map (iterateFrobeniusAlgHom p 1 S) (iterateFrobeniusAlgHom p 1 S) z =
      z ^ p := by
  induction z with
  | zero => rw [map_zero, zero_pow (Nat.Prime.ne_zero Fact.out)]
  | tmul a b =>
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_pow,
        iterateFrobeniusAlgHom_apply, iterateFrobeniusAlgHom_apply, pow_one]
  | add x y hx hy => rw [map_add, hx, hy, add_pow_char]

end TauCeti
