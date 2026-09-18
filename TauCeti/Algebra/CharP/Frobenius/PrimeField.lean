/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.Basic

/-!
# Frobenius over a prime field

The `p`-power Frobenius of a commutative semiring of characteristic `p` fixes the prime field
`ZMod p`, so it is an algebra endomorphism over that field.

## Main declarations

* `TauCeti.primeFieldFrobeniusAlgHom`: the `p`-power map as a prime-field algebra endomorphism.
* `TauCeti.primeFieldFrobeniusAlgHom_apply`: its value on an element.
-/

public section

namespace TauCeti

/-- The `p`-power map as an algebra endomorphism over the prime field `ZMod p`. -/
def primeFieldFrobeniusAlgHom (p : ℕ) [Fact p.Prime] (S : Type*) [CommSemiring S]
    [Algebra (ZMod p) S] [CharP S p] : S →ₐ[ZMod p] S where
  __ := frobenius S p
  commutes' r := by
    have hfrob : frobenius S p (algebraMap (ZMod p) S r) = algebraMap (ZMod p) S r := by
      rw [frobenius_def, ← map_pow, ZMod.pow_card]
    exact hfrob

/-- The underlying function of the prime-field Frobenius algebra endomorphism. -/
theorem coe_primeFieldFrobeniusAlgHom (p : ℕ) [Fact p.Prime] (S : Type*) [CommSemiring S]
    [Algebra (ZMod p) S] [CharP S p] : ⇑(primeFieldFrobeniusAlgHom p S) = (· ^ p) :=
  (rfl)

/-- The prime-field Frobenius algebra endomorphism raises an element to its `p`-th power. -/
@[simp]
theorem primeFieldFrobeniusAlgHom_apply (p : ℕ) [Fact p.Prime] (S : Type*) [CommSemiring S]
    [Algebra (ZMod p) S] [CharP S p] (x : S) : primeFieldFrobeniusAlgHom p S x = x ^ p :=
  congrFun (coe_primeFieldFrobeniusAlgHom p S) x

end TauCeti
