/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Monoid

/-!
# Powers of additive families in a monoid

A family `F : ℕ → N` in a monoid whose zeroth member is one and which turns addition of indices
into multiplication is a monoid homomorphism from the additive natural numbers. Its powers
therefore multiply indices: `(F k) ^ m = F (k * m)`. This file proves that elementary fact once.

## Main results

* `TauCeti.pow_eq_apply_mul_of_map_zero_eq_one_of_map_add_eq_mul`: powers of a
  natural-number-indexed multiplicative family multiply its indices.
-/

public section

namespace TauCeti

/-- **Powers of an additive family in a monoid multiply its indices.** If `F 0 = 1` and
`F (a + b) = F a * F b`, then `(F k) ^ m = F (k * m)`. -/
theorem pow_eq_apply_mul_of_map_zero_eq_one_of_map_add_eq_mul {N : Type*} [Monoid N]
    (F : ℕ → N) (hzero : F 0 = 1)
    (hadd : ∀ a b, F (a + b) = F a * F b) (k m : ℕ) : (F k) ^ m = F (k * m) := by
  induction m with
  | zero => rw [pow_zero, Nat.mul_zero, hzero]
  | succ m ih => rw [pow_succ, ih, Nat.mul_succ, hadd]

end TauCeti
