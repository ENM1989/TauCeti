/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.TensorProduct
public import TauCeti.Algebra.CharP.Frobenius.TensorProduct

/-!
# The Frobenius endomorphism of a commutative bialgebra over a prime field

Let `S` be a commutative bialgebra over `ZMod p`. Its algebra map is injective, so it has
characteristic `p`, and the same applies to its tensor square; therefore the `p`-power
map is a ring endomorphism of both. On the tensor square that endomorphism is the tensor square
of the one on `S`, so the `p`-power map respects comultiplication, and the counit lands in the
prime field, where the `p`-power map is the identity. The `p`-power map is therefore a morphism
of bialgebras.

Contravariantly this is the Frobenius endomorphism of the affine monoid scheme represented by `S`.
When `S` is a Hopf algebra, this is an affine group-scheme endomorphism. On points over a value
algebra of characteristic `p`, it raises every coordinate to its `p`-th power.

## Main declarations

* `TauCeti.primeFieldFrobeniusAlgHom`: the `p`-power map as a prime-field algebra endomorphism.
* `TauCeti.frobeniusBialgHom`: the `p`-power map as a bialgebra endomorphism.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u

variable (p : ℕ) [Fact p.Prime] (S : Type u) [CommSemiring S] [Bialgebra (ZMod p) S]

/-- **The `p`-power map of a commutative bialgebra over the prime field, as a bialgebra
endomorphism.** -/
noncomputable def frobeniusBialgHom : S →ₐc[ZMod p] S :=
  letI : CharP S p :=
    charP_of_injective_algebraMap (Bialgebra.algebraMap_injective (R := ZMod p) S) p
  letI : CharP (S ⊗[ZMod p] S) p :=
    charP_of_injective_algebraMap
      (Bialgebra.algebraMap_injective (R := ZMod p) (S ⊗[ZMod p] S)) p
  BialgHom.ofAlgHom ((primeFieldFrobeniusAlgHom p S) ^ 1)
    (AlgHom.ext fun x => by
      simp only [AlgHom.comp_apply, coe_primeFieldFrobeniusAlgHom,
        pow_one, map_pow, ZMod.pow_card])
    (AlgHom.ext fun x => by
      simpa only [AlgHom.comp_apply,
        pow_one, primeFieldFrobeniusAlgHom_apply, map_pow] using
        (map_primeFieldFrobeniusAlgHom_pow_tensorProduct_apply p S S 1
          ((Bialgebra.comulAlgHom (ZMod p) S) x)))

/-- The Frobenius bialgebra endomorphism raises an element to its `p`-th power. -/
@[simp]
theorem frobeniusBialgHom_apply (x : S) : frobeniusBialgHom p S x = x ^ p := by
  let : CharP S p :=
    charP_of_injective_algebraMap (Bialgebra.algebraMap_injective (R := ZMod p) S) p
  simp only [frobeniusBialgHom, BialgHom.ofAlgHom_apply,
    primeFieldFrobeniusAlgHom_apply, pow_one]

end TauCeti
