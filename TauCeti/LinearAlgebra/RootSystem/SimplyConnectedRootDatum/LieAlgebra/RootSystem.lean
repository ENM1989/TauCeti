/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Isomorphism
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Chevalley

/-!
# The root system of the pinned rational Lie algebra

This file identifies the rational root system attached to a valid Dynkin type with the Killing
root system of its pinned rational Geck Lie algebra. The identification is pinned: on simple roots
it follows the common Bourbaki numbering supplied by `Fin t.rank`.

## Main declarations

* `TauCeti.DynkinType.rationalRootSystemEquiv`: the pinned equivalence from the rational root
  system to the Killing root system of the rational Lie algebra.
-/

public section

namespace TauCeti.DynkinType

open LieAlgebra LieAlgebra.IsKilling

noncomputable section

variable (t : DynkinType) (ht : t.Valid)

/-- The support equivalence between the pinned rational base and the base of the distinguished
Lie-algebra basis, following the common Bourbaki numbering. -/
private def rationalLieBaseSupportEquiv :
    (t.rationalBase ht).support ≃ (t.lieBasis ht).base.support :=
  (t.simpleSupportEquiv ht).symm.trans (t.lieBasis ht).baseSupportEquiv

private theorem cartanMatrix_rationalLieBaseSupportEquiv (i j : (t.rationalBase ht).support) :
    (t.lieBasis ht).base.cartanMatrix (t.rationalLieBaseSupportEquiv ht i)
        (t.rationalLieBaseSupportEquiv ht j) =
      (t.rationalBase ht).cartanMatrix i j := by
  let a := (t.simpleSupportEquiv ht).symm i
  let b := (t.simpleSupportEquiv ht).symm j
  have hi : t.simpleSupportEquiv ht a = i := (t.simpleSupportEquiv ht).apply_symm_apply i
  have hj : t.simpleSupportEquiv ht b = j := (t.simpleSupportEquiv ht).apply_symm_apply j
  rw [← hi, ← hj]
  simp only [rationalLieBaseSupportEquiv, Equiv.trans_apply, Equiv.symm_apply_apply,
    LieAlgebra.Basis.cartanMatrix_base_eq, Matrix.reindex_apply, Matrix.submatrix_apply,
    lieBasis_A_eq, cartanMatrix_rationalBase]

/-- **The pinned rational root system is equivalent to the Killing root system of the pinned
rational Lie algebra.** The equivalence sends each rational simple root to the root attached to
the correspondingly numbered generator of the distinguished Lie-algebra basis. -/
def rationalRootSystemEquiv :
    (t.rationalRootSystem ht).Equiv (rootSystem (t.cartanSubalgebra ht)) :=
  (t.rationalBase ht).equivOfCartanMatrixEq (t.lieBasis ht).base
    (t.rationalLieBaseSupportEquiv ht) (t.cartanMatrix_rationalLieBaseSupportEquiv ht)

/-- The pinned root-system equivalence sends a Bourbaki-numbered simple root to the simple root
of the distinguished Lie-algebra basis with the same number. -/
@[simp] theorem rationalRootSystemEquiv_indexEquiv_simple (i : Fin t.rank) :
    (t.rationalRootSystemEquiv ht).indexEquiv (t.simpleIndex ht i) =
      (t.lieBasis ht).baseSupportEquiv i := by
  simpa only [rationalRootSystemEquiv, rationalLieBaseSupportEquiv, Equiv.trans_apply,
    Equiv.symm_apply_apply, coe_simpleSupportEquiv] using
    equivOfCartanMatrixEq_indexEquiv_apply (t.rationalBase ht) (t.lieBasis ht).base
      (t.rationalLieBaseSupportEquiv ht) (t.cartanMatrix_rationalLieBaseSupportEquiv ht)
      (t.simpleSupportEquiv ht i)

/-- The weight equivalence carries every rational root to the Killing root selected by the root
index equivalence. -/
@[simp] theorem rationalRootSystemEquiv_weightEquiv_root (k : Fin t.numRoots) :
    (t.rationalRootSystemEquiv ht).weightMap ((t.rationalRootSystem ht).root k) =
      (rootSystem (t.cartanSubalgebra ht)).root
        ((t.rationalRootSystemEquiv ht).indexEquiv k) := by
  exact RootPairing.Hom.root_weightMap_apply _ _ k (t.rationalRootSystemEquiv ht).toHom

/-- The covariant inverse coweight equivalence carries every rational coroot to the Killing
coroot selected by the root index equivalence. -/
@[simp] theorem rationalRootSystemEquiv_coweightEquiv_symm_coroot (k : Fin t.numRoots) :
    (t.rationalRootSystemEquiv ht).coweightEquiv.symm
        ((t.rationalRootSystem ht).coroot k) =
      (rootSystem (t.cartanSubalgebra ht)).coroot
        ((t.rationalRootSystemEquiv ht).indexEquiv k) := by
  apply (t.rationalRootSystemEquiv ht).coweightEquiv.injective
  rw [LinearEquiv.apply_symm_apply]
  simpa using (RootPairing.Hom.coroot_coweightMap_apply
    (t.rationalRootSystem ht) (rootSystem (t.cartanSubalgebra ht))
    ((t.rationalRootSystemEquiv ht).indexEquiv k)
    (t.rationalRootSystemEquiv ht).toHom).symm

/-- On a Bourbaki-numbered simple root, the weight equivalence lands at the simple Killing root
of the correspondingly numbered Lie-algebra generator. -/
theorem rationalRootSystemEquiv_weightEquiv_root_simple (i : Fin t.rank) :
    (t.rationalRootSystemEquiv ht).weightMap
        ((t.rationalRootSystem ht).root (t.simpleIndex ht i)) =
      (rootSystem (t.cartanSubalgebra ht)).root
        ((t.lieBasis ht).baseSupportEquiv i) := by
  calc
    _ = (rootSystem (t.cartanSubalgebra ht)).root
        ((t.rationalRootSystemEquiv ht).indexEquiv (t.simpleIndex ht i)) := by
      exact t.rationalRootSystemEquiv_weightEquiv_root ht (t.simpleIndex ht i)
    _ = _ := congrArg _ (t.rationalRootSystemEquiv_indexEquiv_simple ht i)

/-- On a Bourbaki-numbered simple coroot, the covariant inverse coweight equivalence lands at the
simple Killing coroot of the correspondingly numbered Lie-algebra generator. -/
theorem rationalRootSystemEquiv_coweightEquiv_symm_coroot_simple (i : Fin t.rank) :
    (t.rationalRootSystemEquiv ht).coweightEquiv.symm
        ((t.rationalRootSystem ht).coroot (t.simpleIndex ht i)) =
      (rootSystem (t.cartanSubalgebra ht)).coroot
        ((t.lieBasis ht).baseSupportEquiv i) := by
  calc
    _ = (rootSystem (t.cartanSubalgebra ht)).coroot
        ((t.rationalRootSystemEquiv ht).indexEquiv (t.simpleIndex ht i)) := by
      exact t.rationalRootSystemEquiv_coweightEquiv_symm_coroot ht (t.simpleIndex ht i)
    _ = _ := congrArg _ (t.rationalRootSystemEquiv_indexEquiv_simple ht i)

end


end TauCeti.DynkinType
