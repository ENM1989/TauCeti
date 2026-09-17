/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.Field.ZMod

/-!
# Characteristic of an algebra over a prime field

An algebra over `ZMod p` has characteristic `p` as soon as it is nontrivial: the prime field is a
field, so its structure morphism is injective. The trivial ring is the only obstruction, and an
algebra morphism back to `ZMod p` rules it out. A commutative Hopf algebra over `ZMod p` has one —
its counit — and so does a tensor product of two such, so the criterion below is what a
construction over the prime field uses to invoke the Frobenius or a characteristic-`p` identity on
its coordinate algebra.

## Main results

* `TauCeti.charP_of_ringHom_zmod`: a ring morphism back to `ZMod p` supplies nontriviality.
-/

public section

namespace TauCeti

variable (p : ℕ) [Fact p.Prime] {A : Type*} [Semiring A] [Algebra (ZMod p) A]

/-- **An algebra over `ZMod p` admitting a ring morphism back to `ZMod p` has characteristic
`p`.** The morphism supplies nontriviality. -/
theorem charP_of_ringHom_zmod (φ : A →+* ZMod p) : CharP A p := by
  let _ : Nontrivial A := φ.domain_nontrivial
  exact charP_of_injective_algebraMap (algebraMap (ZMod p) A).injective p

end TauCeti
