/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.Frobenius
public import TauCeti.Algebra.Lie.G2.ShortRoot.SpecialIsogeny

/-!
# The special isogeny on the pinned subgroups of the short-root type-G2 carrier

`Matrix.g2SpecialIsogeny` is the matrix formula for the special isogeny `τ` of type `G₂` in
characteristic three, and `TauCeti.G2ShortRoot.points` realizes the short-root carrier's points as
a subgroup of `GL₇`. This file reads the formula on the carrier's four numbered simple root
subgroups and on its split weight torus: the matrix of a numbered simple-root point is the
numbered simple root element matrix of the same parameter, and the matrix of a torus point is the
diagonal matrix of the weight characters, so the pinning equations, the torus equation and the
square relation proved for those matrices become statements about the carrier's own subgroups and
its own Frobenius at exponent one.

Only those elements are covered. The formula is not shown here to be multiplicative, to carry
points of the carrier to points of the carrier, or to have any property at a point outside the
pinned subgroups; the square relation below is the one on those elements, not an identity of
endomorphisms. The carrier is not identified with the pinned simply connected group scheme of type
`G₂`, and constructions made here transfer to that group scheme only along such an identification.

## Main results

* `TauCeti.G2ShortRoot.coe_rootSubgroupPoints_eq_rootElementMatrix` and
  `TauCeti.G2ShortRoot.coe_weightTorusPoints_eq_diagonal`: the matrices of the pinned points.
* `TauCeti.G2ShortRoot.g2SpecialIsogeny_coe_rootSubgroupPoints`: **the pinning equations** on the
  carrier's numbered simple root subgroups, exchanging the two root lengths.
* `TauCeti.G2ShortRoot.g2SpecialIsogeny_coe_weightTorusPoints`: the equation on the weight torus.
* `TauCeti.G2ShortRoot.g2SpecialIsogeny_g2SpecialIsogeny_coe_rootSubgroupPoints`: **the square
  relation** on those subgroups, against the carrier's own Frobenius at exponent one.

## References

* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.
* R. W. Carter, *Simple Groups of Lie Type*, §§12.3 and 13.4.
-/

public section

open Matrix

namespace TauCeti.G2ShortRoot

universe v

variable {A : Type v} [CommRing A]

/-- The matrix of a numbered simple-root point of the short-root carrier is the numbered simple root
element matrix of the same parameter. -/
theorem coe_rootSubgroupPoints_eq_rootElementMatrix (k : Fin 2 ⊕ Fin 2) (u : Multiplicative A) :
    ((rootSubgroupPoints k A u : _root_.Matrix.GeneralLinearGroup (Fin 7) A) :
        Matrix (Fin 7) (Fin 7) A) = rootElementMatrix k (Multiplicative.toAdd u) := by
  rw [coe_rootSubgroupPoints, rootElementMatrix_def]

/-- **The pinning equations of the special isogeny on the carrier's numbered simple root
subgroups**: the numbered simple-root point of index `k` and parameter `u` is carried to the one of
the length-exchanged index, with the parameter raised to the length exponent, three at the short
node and one at the long node. -/
theorem g2SpecialIsogeny_coe_rootSubgroupPoints (k : Fin 2 ⊕ Fin 2) (u : Multiplicative A) :
    g2SpecialIsogeny ((rootSubgroupPoints k A u : _root_.Matrix.GeneralLinearGroup (Fin 7) A) :
        Matrix (Fin 7) (Fin 7) A) =
      ((rootSubgroupPoints (specialIsogenyRootIndex k) A
          (Multiplicative.ofAdd (Multiplicative.toAdd u ^ specialIsogenyExponent k)) :
        _root_.Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) := by
  rw [coe_rootSubgroupPoints_eq_rootElementMatrix, coe_rootSubgroupPoints_eq_rootElementMatrix,
    g2SpecialIsogeny_rootElementMatrix, toAdd_ofAdd]

/-- **The square relation on the carrier's numbered simple root subgroups**: applying the special
isogeny twice to a numbered simple-root point gives the carrier's Frobenius at exponent one of that
point. -/
theorem g2SpecialIsogeny_g2SpecialIsogeny_coe_rootSubgroupPoints [CharP A 3]
    (k : Fin 2 ⊕ Fin 2) (u : Multiplicative A) :
    g2SpecialIsogeny (g2SpecialIsogeny
        ((rootSubgroupPoints k A u : _root_.Matrix.GeneralLinearGroup (Fin 7) A) :
          Matrix (Fin 7) (Fin 7) A)) =
      ((frobenius 3 1 A (rootSubgroupPoints k A u) :
        _root_.Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) := by
  rw [frobenius_rootSubgroupPoints, coe_rootSubgroupPoints_eq_rootElementMatrix,
    coe_rootSubgroupPoints_eq_rootElementMatrix,
    g2SpecialIsogeny_g2SpecialIsogeny_rootElementMatrix, toAdd_ofAdd]
  norm_num

/-- The matrix of a point of the carrier's split weight torus is the diagonal matrix of the weight
characters at that point. -/
theorem coe_weightTorusPoints_eq_diagonal (s : Fin 2 → Aˣ) :
    ((weightTorusPoints A s : _root_.Matrix.GeneralLinearGroup (Fin 7) A) :
        Matrix (Fin 7) (Fin 7) A) =
      Matrix.diagonal fun a => (torusCharacter s (weight a) : A) := by
  rw [coe_weightTorusPoints, TauCeti.UniversalEnvelopingAlgebra.kostantTorusMatrix_apply,
    diagGL_coe]

/-- **The special isogeny on the carrier's weight torus**: a torus point is carried to the point of
the length-exchanged coordinates `(s₁, s₀³)`. -/
theorem g2SpecialIsogeny_coe_weightTorusPoints (s : Fin 2 → Aˣ) :
    g2SpecialIsogeny ((weightTorusPoints A s : _root_.Matrix.GeneralLinearGroup (Fin 7) A) :
        Matrix (Fin 7) (Fin 7) A) =
      ((weightTorusPoints A (specialIsogenyTorusMap s) :
        _root_.Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) := by
  rw [coe_weightTorusPoints_eq_diagonal, coe_weightTorusPoints_eq_diagonal,
    g2SpecialIsogeny_diagonal_torusCharacter]

end TauCeti.G2ShortRoot
