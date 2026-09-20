/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Weights.Root.KostantStability
public import TauCeti.LinearAlgebra.RootSystem.EquivInvariance
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.F4.RootString
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.RootSystem

/-!
# Exact low-degree Chevalley action in type F₄

This file transports the pinned forty-eight-root indexing to the rational Killing root system and
records the exact degree-one and degree-two adjoint actions needed for the characteristic-two
short-root submodule. The root-string coefficients come from structural F₄ length arguments; no
matrix or root-table certificate is used.
-/

public section

namespace TauCeti.DynkinType

open _root_.LieAlgebra _root_.LieAlgebra.IsKilling LieModule

noncomputable section

/-- Identify the fixed forty-eight F₄ root labels with the root index of `DynkinType.F4`. -/
abbrev f4RootIndex (i : Fin 48) : Fin F4.numRoots :=
  Fin.cast numRoots_F4.symm i

/-- The Killing-root label belonging to a pinned integral root index. -/
abbrev f4KillingRootLabel (i : Fin 48) :
    (F4.cartanSubalgebra valid_F4).root :=
  (F4.rationalRootSystemEquiv valid_F4).indexEquiv (f4RootIndex i)

/-- The Killing weight indexed by the corresponding root of the pinned F₄ root datum. -/
abbrev f4KillingRoot (i : Fin 48) :
    Weight ℚ (F4.cartanSubalgebra valid_F4) (F4.lieAlgebra valid_F4) :=
  (f4KillingRootLabel i : (F4.cartanSubalgebra valid_F4).root)

/-- A chosen F₄ root-vector system compatible with the pinned Chevalley involution. -/
noncomputable def f4ChevalleyRootVector :
    Weight ℚ (F4.cartanSubalgebra valid_F4) (F4.lieAlgebra valid_F4) →
      F4.lieAlgebra valid_F4 :=
  Classical.choose (F4.exists_isChevalleySystem valid_F4)

/-- The chosen F₄ root vectors form a Chevalley system for the pinned involution. -/
theorem f4ChevalleyRootVector_isChevalleySystem :
    IsChevalleySystem (F4.chevalleyInvolution valid_F4) f4ChevalleyRootVector :=
  Classical.choose_spec (F4.exists_isChevalleySystem valid_F4)

/-- Integral root addition transports to addition of the corresponding rational Killing weights. -/
theorem f4KillingRoot_eq_add_zsmul (α β γ : Fin 48) (n : ℤ)
    (h : f4SimplyConnectedRootDatum.root γ =
      f4SimplyConnectedRootDatum.root β + n • f4SimplyConnectedRootDatum.root α) :
    (f4KillingRoot γ : (F4.cartanSubalgebra valid_F4) → ℚ) =
      (f4KillingRoot β : (F4.cartanSubalgebra valid_F4) → ℚ) +
        (n : ℚ) • (f4KillingRoot α : (F4.cartanSubalgebra valid_F4) → ℚ) := by
  let E := F4.rationalRootSystemEquiv valid_F4
  have hint : (F4.simplyConnectedRootDatum valid_F4).root (f4RootIndex γ) =
      (F4.simplyConnectedRootDatum valid_F4).root (f4RootIndex β) +
        n • (F4.simplyConnectedRootDatum valid_F4).root (f4RootIndex α) := by
    rw [simplyConnectedRootDatum_F4]
    simp only [rank_F4]
    convert h using 1 <;> congr
  have hrat : (F4.rationalRootSystem valid_F4).root (f4RootIndex γ) =
      (F4.rationalRootSystem valid_F4).root (f4RootIndex β) +
        (n : ℚ) • (F4.rationalRootSystem valid_F4).root (f4RootIndex α) := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply]
    rw [F4.root_rationalRootSystem valid_F4, F4.root_rationalRootSystem valid_F4,
      F4.root_rationalRootSystem valid_F4]
    have hi := congrFun hint i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi ⊢
    exact_mod_cast hi
  have hmap (i : Fin 48) :
      E.weightEquiv ((F4.rationalRootSystem valid_F4).root (f4RootIndex i)) =
        (rootSystem (F4.cartanSubalgebra valid_F4)).root
          (E.indexEquiv (f4RootIndex i)) :=
    RootPairing.Hom.root_weightMap_apply _ _ (f4RootIndex i) E.toHom
  have hmapped :
      (rootSystem (F4.cartanSubalgebra valid_F4)).root (E.indexEquiv (f4RootIndex γ)) =
        (rootSystem (F4.cartanSubalgebra valid_F4)).root (E.indexEquiv (f4RootIndex β)) +
          (n : ℚ) • (rootSystem (F4.cartanSubalgebra valid_F4)).root
            (E.indexEquiv (f4RootIndex α)) := by
    calc
      _ = E.weightEquiv ((F4.rationalRootSystem valid_F4).root (f4RootIndex γ)) :=
        (hmap γ).symm
      _ = E.weightEquiv ((F4.rationalRootSystem valid_F4).root (f4RootIndex β) +
          (n : ℚ) • (F4.rationalRootSystem valid_F4).root (f4RootIndex α)) :=
        congrArg E.weightEquiv hrat
      _ = E.weightEquiv ((F4.rationalRootSystem valid_F4).root (f4RootIndex β)) +
          (n : ℚ) • E.weightEquiv
            ((F4.rationalRootSystem valid_F4).root (f4RootIndex α)) := by
        calc
          _ = E.weightEquiv ((F4.rationalRootSystem valid_F4).root (f4RootIndex β)) +
              E.weightEquiv ((n : ℚ) •
                (F4.rationalRootSystem valid_F4).root (f4RootIndex α)) :=
            E.weightEquiv.map_add _ _
          _ = _ := congrArg
            (E.weightEquiv ((F4.rationalRootSystem valid_F4).root (f4RootIndex β)) + ·)
            (E.weightEquiv.map_smul (n : ℚ)
              ((F4.rationalRootSystem valid_F4).root (f4RootIndex α)))
      _ = _ := congrArg₂ (· + ·) (hmap β) (congrArg ((n : ℚ) • ·) (hmap α))
  apply funext
  intro y
  have hy := congrArg
    (fun f : Module.Dual ℚ (F4.cartanSubalgebra valid_F4) => f y) hmapped
  simpa only [rootSystem_root_apply, LinearMap.add_apply, LinearMap.smul_apply,
    Pi.add_apply, Pi.smul_apply, Weight.toLinear_apply, f4KillingRoot] using hy

/-- Addition of rational Killing roots reflects the corresponding pinned integral root
identity. -/
theorem f4Root_eq_add_of_f4KillingRoot_eq_add (α β γ : Fin 48)
    (h : (f4KillingRoot γ : (F4.cartanSubalgebra valid_F4) → ℚ) =
      (f4KillingRoot β : (F4.cartanSubalgebra valid_F4) → ℚ) +
        (f4KillingRoot α : (F4.cartanSubalgebra valid_F4) → ℚ)) :
    f4SimplyConnectedRootDatum.root γ =
      f4SimplyConnectedRootDatum.root β + f4SimplyConnectedRootDatum.root α := by
  let E := F4.rationalRootSystemEquiv valid_F4
  have hmap (i : Fin 48) :
      E.weightEquiv ((F4.rationalRootSystem valid_F4).root (f4RootIndex i)) =
        (rootSystem (F4.cartanSubalgebra valid_F4)).root
          (E.indexEquiv (f4RootIndex i)) :=
    RootPairing.Hom.root_weightMap_apply _ _ (f4RootIndex i) E.toHom
  have hmapped :
      E.weightEquiv ((F4.rationalRootSystem valid_F4).root (f4RootIndex γ)) =
        E.weightEquiv ((F4.rationalRootSystem valid_F4).root (f4RootIndex β)) +
          E.weightEquiv ((F4.rationalRootSystem valid_F4).root (f4RootIndex α)) := by
    calc
      _ = (rootSystem (F4.cartanSubalgebra valid_F4)).root
          (E.indexEquiv (f4RootIndex γ)) := hmap γ
      _ = (rootSystem (F4.cartanSubalgebra valid_F4)).root
          (E.indexEquiv (f4RootIndex β)) +
            (rootSystem (F4.cartanSubalgebra valid_F4)).root
              (E.indexEquiv (f4RootIndex α)) := by
        apply LinearMap.ext
        intro y
        have hy := congrFun h y
        simpa only [rootSystem_root_apply, LinearMap.add_apply, Pi.add_apply,
          Weight.toLinear_apply, f4KillingRoot] using hy
      _ = _ := congrArg₂ (· + ·) (hmap β).symm (hmap α).symm
  have hrat : (F4.rationalRootSystem valid_F4).root (f4RootIndex γ) =
      (F4.rationalRootSystem valid_F4).root (f4RootIndex β) +
        (F4.rationalRootSystem valid_F4).root (f4RootIndex α) := by
    apply E.weightEquiv.injective
    rw [E.weightEquiv.map_add]
    exact hmapped
  have hint : (F4.simplyConnectedRootDatum valid_F4).root (f4RootIndex γ) =
      (F4.simplyConnectedRootDatum valid_F4).root (f4RootIndex β) +
        (F4.simplyConnectedRootDatum valid_F4).root (f4RootIndex α) := by
    ext i
    have hi := congrFun hrat i
    simp only [Pi.add_apply] at hi ⊢
    rw [F4.root_rationalRootSystem valid_F4, F4.root_rationalRootSystem valid_F4,
      F4.root_rationalRootSystem valid_F4] at hi
    exact_mod_cast hi
  rw [simplyConnectedRootDatum_F4] at hint
  simp only [rank_F4] at hint ⊢
  convert hint using 1 <;> congr

/-- Addition by an integral multiple of a rational Killing root reflects the corresponding
pinned integral root identity. -/
theorem f4Root_eq_add_zsmul_of_f4KillingRoot_eq_add_zsmul
    (α β γ : Fin 48) (n : ℤ)
    (h : (f4KillingRoot γ : (F4.cartanSubalgebra valid_F4) → ℚ) =
      (f4KillingRoot β : (F4.cartanSubalgebra valid_F4) → ℚ) +
        (n : ℚ) • (f4KillingRoot α : (F4.cartanSubalgebra valid_F4) → ℚ)) :
    f4SimplyConnectedRootDatum.root γ =
      f4SimplyConnectedRootDatum.root β + n • f4SimplyConnectedRootDatum.root α := by
  let E := F4.rationalRootSystemEquiv valid_F4
  have hmap (i : Fin 48) :
      E.weightEquiv ((F4.rationalRootSystem valid_F4).root (f4RootIndex i)) =
        (rootSystem (F4.cartanSubalgebra valid_F4)).root
          (E.indexEquiv (f4RootIndex i)) :=
    RootPairing.Hom.root_weightMap_apply _ _ (f4RootIndex i) E.toHom
  have hmapped :
      E.weightEquiv ((F4.rationalRootSystem valid_F4).root (f4RootIndex γ)) =
        E.weightEquiv ((F4.rationalRootSystem valid_F4).root (f4RootIndex β)) +
          (n : ℚ) • E.weightEquiv
            ((F4.rationalRootSystem valid_F4).root (f4RootIndex α)) := by
    calc
      _ = (rootSystem (F4.cartanSubalgebra valid_F4)).root
          (E.indexEquiv (f4RootIndex γ)) := hmap γ
      _ = (rootSystem (F4.cartanSubalgebra valid_F4)).root
          (E.indexEquiv (f4RootIndex β)) + (n : ℚ) •
            (rootSystem (F4.cartanSubalgebra valid_F4)).root
              (E.indexEquiv (f4RootIndex α)) := by
        apply LinearMap.ext
        intro y
        have hy := congrFun h y
        simpa only [rootSystem_root_apply, LinearMap.add_apply, LinearMap.smul_apply,
          Pi.add_apply, Pi.smul_apply, Weight.toLinear_apply, f4KillingRoot] using hy
      _ = _ := congrArg₂ (· + ·) (hmap β).symm
        (congrArg ((n : ℚ) • ·) (hmap α).symm)
  have hrat : (F4.rationalRootSystem valid_F4).root (f4RootIndex γ) =
      (F4.rationalRootSystem valid_F4).root (f4RootIndex β) +
        (n : ℚ) • (F4.rationalRootSystem valid_F4).root (f4RootIndex α) := by
    apply E.weightEquiv.injective
    rw [E.weightEquiv.map_add, E.weightEquiv.map_smul]
    exact hmapped
  have hint : (F4.simplyConnectedRootDatum valid_F4).root (f4RootIndex γ) =
      (F4.simplyConnectedRootDatum valid_F4).root (f4RootIndex β) +
        n • (F4.simplyConnectedRootDatum valid_F4).root (f4RootIndex α) := by
    ext i
    have hi := congrFun hrat i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi ⊢
    rw [F4.root_rationalRootSystem valid_F4, F4.root_rationalRootSystem valid_F4,
      F4.root_rationalRootSystem valid_F4] at hi
    exact_mod_cast hi
  rw [simplyConnectedRootDatum_F4] at hint
  simp only [rank_F4] at hint ⊢
  convert hint using 1 <;> congr

/-- The rational Killing-root identification preserves the root-string coefficient inherited from
the integral pinned F₄ datum. -/
theorem f4KillingRootSystem_chainBotCoeff (α β : Fin 48) :
    (rootSystem (F4.cartanSubalgebra valid_F4)).chainBotCoeff
        ((F4.rationalRootSystemEquiv valid_F4).indexEquiv (f4RootIndex α))
        ((F4.rationalRootSystemEquiv valid_F4).indexEquiv (f4RootIndex β)) =
      f4SimplyConnectedRootDatum.chainBotCoeff α β := by
  calc
    _ = (F4.rationalRootSystem valid_F4).chainBotCoeff
        (f4RootIndex α) (f4RootIndex β) :=
      chainBotCoeff_indexEquiv (F4.rationalRootSystemEquiv valid_F4)
        (f4RootIndex α) (f4RootIndex β)
    _ = (F4.simplyConnectedRootDatum valid_F4).chainBotCoeff
        (f4RootIndex α) (f4RootIndex β) :=
      by
        change (rootPairingBaseChange ℚ (F4.simplyConnectedRootDatum valid_F4)
          (toLinearMap_simplyConnectedRootDatum F4 valid_F4)).chainBotCoeff
            (f4RootIndex α) (f4RootIndex β) = _
        exact chainBotCoeff_rootPairingBaseChange ..
    _ = _ := by
      rw [simplyConnectedRootDatum_F4]
      congr

/-- The rational Killing-root identification preserves the ascending root-string coefficient
inherited from the integral pinned F₄ datum. -/
theorem f4KillingRootSystem_chainTopCoeff (α β : Fin 48) :
    (rootSystem (F4.cartanSubalgebra valid_F4)).chainTopCoeff
        ((F4.rationalRootSystemEquiv valid_F4).indexEquiv (f4RootIndex α))
        ((F4.rationalRootSystemEquiv valid_F4).indexEquiv (f4RootIndex β)) =
      f4SimplyConnectedRootDatum.chainTopCoeff α β := by
  calc
    _ = (F4.rationalRootSystem valid_F4).chainTopCoeff
        (f4RootIndex α) (f4RootIndex β) :=
      chainTopCoeff_indexEquiv (F4.rationalRootSystemEquiv valid_F4)
        (f4RootIndex α) (f4RootIndex β)
    _ = (F4.simplyConnectedRootDatum valid_F4).chainTopCoeff
        (f4RootIndex α) (f4RootIndex β) :=
      by
        change (rootPairingBaseChange ℚ (F4.simplyConnectedRootDatum valid_F4)
          (toLinearMap_simplyConnectedRootDatum F4 valid_F4)).chainTopCoeff
            (f4RootIndex α) (f4RootIndex β) = _
        exact chainTopCoeff_rootPairingBaseChange ..
    _ = _ := by
      rw [simplyConnectedRootDatum_F4]
      congr

/-- Every Killing coroot expands in the simple Killing coroots with the coordinates of the
corresponding pinned integral F₄ coroot. -/
theorem f4KillingCoroot_eq_sum_simple (β : Fin 48) :
    (rootSystem (F4.cartanSubalgebra valid_F4)).coroot (f4KillingRootLabel β) =
      ∑ i : Fin F4.rank,
        ((F4.rationalRootSystem valid_F4).coroot (f4RootIndex β) i) •
          (rootSystem (F4.cartanSubalgebra valid_F4)).coroot
            ((F4.lieBasis valid_F4).baseSupportEquiv i) := by
  let E := F4.rationalRootSystemEquiv valid_F4
  let k := f4RootIndex β
  have hsimple (i : Fin F4.rank) :
      (F4.rationalRootSystem valid_F4).coroot (F4.simpleSupportEquiv valid_F4 i) =
        Pi.single i 1 := by
    ext j
    simp only [coroot_rationalRootSystem, coe_simpleSupportEquiv, coroot_simpleIndex]
    by_cases hij : i = j
    · subst j
      rw [Pi.single_eq_same, Pi.single_eq_same]
      norm_num
    · rw [Pi.single_eq_of_ne (Ne.symm hij), Pi.single_eq_of_ne (Ne.symm hij)]
      norm_num
  have hsource : (F4.rationalRootSystem valid_F4).coroot k =
      ∑ i : Fin F4.rank, ((F4.rationalRootSystem valid_F4).coroot k i) •
        (F4.rationalRootSystem valid_F4).coroot
          (F4.simpleSupportEquiv valid_F4 i) := by
    calc
      _ = ∑ i, ((F4.rationalRootSystem valid_F4).coroot k i) • Pi.single i 1 :=
        pi_eq_sum_univ' ((F4.rationalRootSystem valid_F4).coroot k)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        exact congrArg (((F4.rationalRootSystem valid_F4).coroot k i) • ·)
          (hsimple i).symm
  calc
    _ = E.coweightEquiv.symm ((F4.rationalRootSystem valid_F4).coroot k) :=
      by
      apply E.coweightEquiv.injective
      rw [LinearEquiv.apply_symm_apply, RootPairing.Equiv.coweightEquiv_apply]
      simpa only [f4KillingRootLabel, E, k, Equiv.symm_apply_apply] using
        RootPairing.Hom.coroot_coweightMap_apply _ _ (E.indexEquiv k) E.toHom
    _ = E.coweightEquiv.symm (∑ i : Fin F4.rank,
        ((F4.rationalRootSystem valid_F4).coroot k i) •
          (F4.rationalRootSystem valid_F4).coroot
            (F4.simpleSupportEquiv valid_F4 i)) := congrArg E.coweightEquiv.symm hsource
    _ = ∑ i : Fin F4.rank, ((F4.rationalRootSystem valid_F4).coroot k i) •
        E.coweightEquiv.symm ((F4.rationalRootSystem valid_F4).coroot
          (F4.simpleSupportEquiv valid_F4 i)) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply congrArg (((F4.rationalRootSystem valid_F4).coroot k i) • ·)
      simpa only [coe_simpleSupportEquiv] using
        F4.rationalRootSystemEquiv_coweightEquiv_symm_coroot_simpleIndex valid_F4 i

/-- The Cartan integer of a pinned Killing root against a simple Killing coroot is the
corresponding integral pairing in the pinned F₄ datum. -/
theorem f4RootCartanWeight_simple (α : Fin 48) (i : Fin F4.rank) :
    rootCartanWeight (f4KillingRoot α)
        (((F4.lieBasis valid_F4).baseSupportEquiv i :
          (F4.cartanSubalgebra valid_F4).root) :
            Weight ℚ (F4.cartanSubalgebra valid_F4) (F4.lieAlgebra valid_F4)) =
      f4SimplyConnectedRootDatum.pairing α
        (Fin.castAdd 44 (Fin.cast rank_F4 i)) := by
  apply (Int.cast_injective : Function.Injective (fun z : ℤ => (z : ℚ)))
  rw [intCast_rootCartanWeight_apply]
  change (rootSystem (F4.cartanSubalgebra valid_F4)).pairing
      (f4KillingRootLabel α) ((F4.lieBasis valid_F4).baseSupportEquiv i) = _
  rw [← F4.rationalRootSystemEquiv_indexEquiv_simpleIndex valid_F4 i,
    (F4.rationalRootSystemEquiv valid_F4).toHom.pairing,
    F4.pairing_rationalRootSystem, simplyConnectedRootDatum_F4]
  norm_cast
  have hs : F4.simpleIndex valid_F4 i =
      Fin.castAdd 44 (Fin.cast rank_F4 i) := by
    have hi : i = Fin.cast rank_F4 i := by
      apply Fin.ext
      rfl
    rw [hi]
    exact simpleIndex_F4 valid_F4 (Fin.cast rank_F4 i)
  rw [hs]
  congr 1

/-- The bracket along any nondegenerate F₄ root edge has the integral Chevalley coefficient
prescribed by the descending root string. This packages the index transport once, so subsequent
characteristic-two arguments can use root lengths to determine only the structural coefficient. -/
theorem f4_lie_rootVector_of_add (α β γ : Fin 48)
    (h : f4SimplyConnectedRootDatum.root γ =
      f4SimplyConnectedRootDatum.root β + f4SimplyConnectedRootDatum.root α) :
    ∃ z : ℤ, z.natAbs = f4SimplyConnectedRootDatum.chainBotCoeff α β + 1 ∧
      ⁅f4ChevalleyRootVector (f4KillingRoot α),
          f4ChevalleyRootVector (f4KillingRoot β)⁆ =
        (z : ℚ) • f4ChevalleyRootVector (f4KillingRoot γ) := by
  let H := F4.cartanSubalgebra valid_F4
  let L := F4.lieAlgebra valid_F4
  let E := F4.rationalRootSystemEquiv valid_F4
  let P := rootSystem H
  let a : Weight ℚ H L := f4KillingRoot α
  let b : Weight ℚ H L := f4KillingRoot β
  let g : Weight ℚ H L := f4KillingRoot γ
  let x := f4ChevalleyRootVector
  have hx : IsChevalleySystem (F4.chevalleyInvolution valid_F4) x :=
    f4ChevalleyRootVector_isChevalleySystem
  have ha : a.IsNonZero := by
    simpa only [a, f4KillingRoot] using
      LieSubalgebra.isNonZero_coe_root (E.indexEquiv (f4RootIndex α))
  have hb : b.IsNonZero := by
    simpa only [b, f4KillingRoot] using
      LieSubalgebra.isNonZero_coe_root (E.indexEquiv (f4RootIndex β))
  have hg : g.IsNonZero := by
    simpa only [g, f4KillingRoot] using
      LieSubalgebra.isNonZero_coe_root (E.indexEquiv (f4RootIndex γ))
  have hgab : (g : H → ℚ) = (a : H → ℚ) + b := by
    have hmap := f4KillingRoot_eq_add_zsmul α β γ 1 (by
      simpa only [one_zsmul] using h)
    have hmap' : (g : H → ℚ) = (b : H → ℚ) + a := by
      simpa only [H, a, b, g, Int.cast_one, one_smul] using hmap
    exact hmap'.trans (add_comm _ _)
  let ia := E.indexEquiv (f4RootIndex α)
  let ib := E.indexEquiv (f4RootIndex β)
  let ig := E.indexEquiv (f4RootIndex γ)
  have hroot : P.root ig = P.root ia + P.root ib := by
    ext y
    simpa only [P, ia, ib, ig, a, b, g, rootSystem_root_apply,
      Weight.toLinear_apply, LinearMap.add_apply, Pi.add_apply] using congrFun hgab y
  have hlin := P.linearIndependent_of_add_mem_range_root' ⟨ig, hroot⟩
  have hcoeff := rootSystem_chainCoeffs_eq ha hb (by
    simpa only [P, ia, ib, a, b, rootSystem_root_apply, Weight.toLinear_apply] using hlin)
  have hLieBot : chainBotCoeff (a : H → ℚ) b =
      f4SimplyConnectedRootDatum.chainBotCoeff α β := by
    rw [← hcoeff.2]
    change P.chainBotCoeff ia ib = _
    simpa only [P, ia, ib, E] using f4KillingRootSystem_chainBotCoeff α β
  let N := hx.intStructureConstant a b g hg hgab
  have hN := hx.intStructureConstant_eq_natCast_or_eq_neg_natCast a b g ha hb hg hgab
  have hlie := hx.lie_eq_intStructureConstant_zsmul a b g hg hgab
  refine ⟨N, ?_, ?_⟩
  · rcases hN with hN | hN
    · change (hx.intStructureConstant a b g hg hgab).natAbs = _
      rw [hN, Int.natAbs_natCast, hLieBot]
    · change (hx.intStructureConstant a b g hg hgab).natAbs = _
      rw [hN, Int.natAbs_neg, Int.natAbs_natCast, hLieBot]
  · simpa only [N, Int.cast_smul_eq_zsmul] using hlie

/-- A root edge whose descending string has length zero carries a unit Chevalley coefficient. -/
theorem f4_lie_rootVector_of_add_of_chainBotCoeff_eq_zero (α β γ : Fin 48)
    (hbot : f4SimplyConnectedRootDatum.chainBotCoeff α β = 0)
    (h : f4SimplyConnectedRootDatum.root γ =
      f4SimplyConnectedRootDatum.root β + f4SimplyConnectedRootDatum.root α) :
    ∃ ε : ℤ, ε.natAbs = 1 ∧
      ⁅f4ChevalleyRootVector (f4KillingRoot α),
          f4ChevalleyRootVector (f4KillingRoot β)⁆ =
        (ε : ℚ) • f4ChevalleyRootVector (f4KillingRoot γ) := by
  obtain ⟨ε, hε, hlie⟩ := f4_lie_rootVector_of_add α β γ h
  refine ⟨ε, ?_, hlie⟩
  simpa only [hbot, zero_add] using hε

/-- A short--short bracket landing in a long F₄ root has coefficient of absolute value two.
Consequently this bracket vanishes after reducing the integral Chevalley lattice modulo two. -/
theorem f4_lie_rootVector_of_short_add_short_eq_long (α β γ : Fin 48)
    (hα : f4Length α = 1) (hβ : f4Length β = 1) (hγ : f4Length γ = 2)
    (h : f4SimplyConnectedRootDatum.root γ =
      f4SimplyConnectedRootDatum.root β + f4SimplyConnectedRootDatum.root α) :
    ∃ z : ℤ, z.natAbs = 2 ∧
      ⁅f4ChevalleyRootVector (f4KillingRoot α),
          f4ChevalleyRootVector (f4KillingRoot β)⁆ =
        (z : ℚ) • f4ChevalleyRootVector (f4KillingRoot γ) := by
  obtain ⟨z, hz, hlie⟩ := f4_lie_rootVector_of_add α β γ h
  refine ⟨z, ?_, hlie⟩
  rw [hz, f4_chainBotCoeff_eq_one_of_short_add_short_eq_long α β γ hα hβ hγ h]

/-- Along a two-step F₄ string from a long root in a short-root direction, the square of the
adjoint root-vector action has coefficient of absolute value two. Dividing by `2!` therefore has
unit coefficient, which becomes exactly one after reduction modulo two. -/
theorem f4_ad_sq_rootVector_of_long_add_two_short (α β γ : Fin 48)
    (hα : f4Length α = 1) (hβ : f4Length β = 2)
    (h : f4SimplyConnectedRootDatum.root γ =
      f4SimplyConnectedRootDatum.root β +
        (2 : ℤ) • f4SimplyConnectedRootDatum.root α) :
    ∃ z : ℤ, z.natAbs = 2 ∧
      ((ad ℚ (F4.lieAlgebra valid_F4)
          (f4ChevalleyRootVector (f4KillingRoot α))) ^ 2)
          (f4ChevalleyRootVector (f4KillingRoot β)) =
        (z : ℚ) • f4ChevalleyRootVector (f4KillingRoot γ) := by
  let L := F4.lieAlgebra valid_F4
  let a := f4KillingRoot α
  let b := f4KillingRoot β
  let g := f4KillingRoot γ
  let x := f4ChevalleyRootVector
  obtain ⟨δ, hδ, -, hbotab, -, hbotad, -⟩ :=
    exists_f4_short_midpoint_of_long_add_two_short α β γ hα hβ h
  have hγδ : f4SimplyConnectedRootDatum.root γ =
      f4SimplyConnectedRootDatum.root δ + f4SimplyConnectedRootDatum.root α := by
    rw [h, hδ]
    module
  obtain ⟨N₁, hN₁, hlie₁⟩ := f4_lie_rootVector_of_add α β δ hδ
  obtain ⟨N₂, hN₂, hlie₂⟩ := f4_lie_rootVector_of_add α δ γ hγδ
  have hN₁' : N₁.natAbs = 1 := by simpa only [hbotab, zero_add] using hN₁
  have hN₂' : N₂.natAbs = 2 := by simpa only [hbotad, one_add_one_eq_two] using hN₂
  refine ⟨N₁ * N₂, ?_, ?_⟩
  · rw [Int.natAbs_mul, hN₁', hN₂']
  · change ((ad ℚ L (x a)) ^ 2) (x b) = ((N₁ * N₂ : ℤ) : ℚ) • x g
    rw [pow_two, Module.End.mul_apply, ad_apply, ad_apply, hlie₁, lie_smul, hlie₂,
      smul_smul, Int.cast_mul]

/-- The second divided adjoint power along a long--short--long F₄ string has unit coefficient.
After reduction modulo two the sign disappears, so this is the structural source of the quadratic
term in the exceptional isogeny pinning formula. -/
theorem f4_dividedAd_sq_rootVector_of_long_add_two_short (α β γ : Fin 48)
    (hα : f4Length α = 1) (hβ : f4Length β = 2)
    (h : f4SimplyConnectedRootDatum.root γ =
      f4SimplyConnectedRootDatum.root β +
        (2 : ℤ) • f4SimplyConnectedRootDatum.root α) :
    ∃ ε : ℤ, ε.natAbs = 1 ∧
      ((Nat.factorial 2 : ℚ)⁻¹ •
          ((ad ℚ (F4.lieAlgebra valid_F4)
            (f4ChevalleyRootVector (f4KillingRoot α))) ^ 2)
            (f4ChevalleyRootVector (f4KillingRoot β))) =
        (ε : ℚ) • f4ChevalleyRootVector (f4KillingRoot γ) := by
  obtain ⟨z, hzabs, hz⟩ := f4_ad_sq_rootVector_of_long_add_two_short α β γ hα hβ h
  have hzsign : z = 2 ∨ z = -2 := by omega
  rcases hzsign with rfl | rfl
  · refine ⟨1, by norm_num, ?_⟩
    rw [hz]
    rw [smul_smul]
    norm_num
  · refine ⟨-1, by norm_num, ?_⟩
    rw [hz]
    rw [smul_smul]
    norm_num

end

end TauCeti.DynkinType
