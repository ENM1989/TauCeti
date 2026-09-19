/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.F4.Length
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.NonSimplyLaced
public import TauCeti.LinearAlgebra.RootSystem.InvariantForm.RootString

/-!
# Root strings in the pinned F₄ root system

This file derives root-string bounds from the invariant root-length identity. The proofs use the
abstract root-system API after the pinned length table has supplied the two possible squared
lengths. They avoid case splits over the forty-eight root coordinates.

The initial results cover the strings needed to construct the characteristic-two short-root
submodule. In particular, a short-short bracket landing in a long root has absolute structure
constant two, while a long-root direction preserves the short-root span.
-/

public section

namespace TauCeti.DynkinType

/-- The tabulated F4 root length is quadratic along every integral root relation. -/
theorem f4Length_of_root_eq_add_zsmul (α β γ : Fin 48) (n : ℤ)
    (h : f4SimplyConnectedRootDatum.root γ =
      f4SimplyConnectedRootDatum.root β + n • f4SimplyConnectedRootDatum.root α) :
    f4Length γ = f4Length β + n * f4Length α *
      f4SimplyConnectedRootDatum.pairing β α + n ^ 2 * f4Length α :=
  f4SimplyConnectedRootDatum.length_of_root_eq_add_zsmul f4Length
    f4Length_mul_pairing_comm α β γ n h


/-- Distinct non-opposite short F4 roots have Cartan pairing `-1`, `0`, or `1`. -/
theorem f4_pairing_mem_neg_one_zero_one_of_short (α β : Fin 48)
    (hα : f4Length α = 1) (hβ : f4Length β = 1) (hne : β ≠ α)
    (hneg : f4SimplyConnectedRootDatum.root β ≠
      -f4SimplyConnectedRootDatum.root α) :
    f4SimplyConnectedRootDatum.pairing β α ∈ ({-1, 0, 1} : Set ℤ) := by
  let P := f4SimplyConnectedRootDatum
  have hsym : P.pairing β α = P.pairing α β := by
    have h := f4Length_mul_pairing_comm α β
    rw [hα, hβ, one_mul, one_mul] at h
    simpa only [P] using h
  have hbdd : |P.pairing β α| ≤ 2 := by
    simpa only [P] using abs_pairing_f4SimplyConnectedRootDatum_le_two β α
  have hne_two : P.pairing β α ≠ 2 := by
    intro htwo
    have : β = α := (P.pairing_two_two_iff β α).mp ⟨htwo, hsym.symm.trans htwo⟩
    exact hne this
  have hne_neg_two : P.pairing β α ≠ -2 := by
    intro htwo
    have : P.root β = -P.root α :=
      (P.pairing_neg_two_neg_two_iff β α).mp ⟨htwo, hsym.symm.trans htwo⟩
    exact hneg this
  have hresult : P.pairing β α ∈ ({-1, 0, 1} : Set ℤ) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    have hbounds : -2 ≤ P.pairing β α ∧ P.pairing β α ≤ 2 := abs_le.mp hbdd
    omega
  simpa only [P] using hresult

/-- A root string through two distinct, non-opposite short F4 roots has no term
two or more steps in the positive direction. -/
theorem f4_not_root_eq_short_add_nsmul_short_of_two_le (α β γ : Fin 48) (n : ℕ)
    (hα : f4Length α = 1) (hβ : f4Length β = 1)
    (hneg : f4SimplyConnectedRootDatum.root β ≠
      -f4SimplyConnectedRootDatum.root α) (hn : 2 ≤ n)
    (h : f4SimplyConnectedRootDatum.root γ =
      f4SimplyConnectedRootDatum.root β +
        (n : ℤ) • f4SimplyConnectedRootDatum.root α) : False := by
  have hn' : (2 : ℤ) ≤ n := by exact_mod_cast hn
  have hne : β ≠ α := by
    intro hβα
    subst β
    have hlen := f4Length_of_root_eq_add_zsmul α α γ n h
    rcases f4Length_eq_one_or_eq_two γ with hγ | hγ <;>
      rw [hα, hγ, f4SimplyConnectedRootDatum.pairing_same] at hlen <;>
      norm_num at hlen <;>
      nlinarith
  have hp := f4_pairing_mem_neg_one_zero_one_of_short α β hα hβ hne hneg
  have hlen := f4Length_of_root_eq_add_zsmul α β γ n h
  rcases f4Length_eq_one_or_eq_two γ with hγ | hγ <;>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp <;>
    rcases hp with hp | hp | hp <;>
    rw [hα, hβ, hγ, hp] at hlen <;>
    norm_num at hlen <;>
    nlinarith [sq_nonneg ((n : ℤ) - 1)]

/-- When the sum of two short F4 roots is long, their Cartan pairing is zero. -/
theorem f4_pairing_eq_zero_of_short_add_short_eq_long (α β γ : Fin 48)
    (hα : f4Length α = 1) (hβ : f4Length β = 1) (hγ : f4Length γ = 2)
    (h : f4SimplyConnectedRootDatum.root γ =
      f4SimplyConnectedRootDatum.root β + f4SimplyConnectedRootDatum.root α) :
    f4SimplyConnectedRootDatum.pairing β α = 0 := by
  have hlen := f4Length_of_root_eq_add_zsmul α β γ 1 (by simpa using h)
  rw [hα, hβ, hγ] at hlen
  norm_num at hlen ⊢
  omega

/-- A positive root string from a short root in a long-root direction has at most
one step, and that step is again short. -/
theorem f4_n_eq_one_and_pairing_eq_neg_one_and_length_eq_one_of_short_add_nsmul_long
    (α β γ : Fin 48) (n : ℕ)
    (hα : f4Length α = 2) (hβ : f4Length β = 1) (hn : 0 < n)
    (h : f4SimplyConnectedRootDatum.root γ =
      f4SimplyConnectedRootDatum.root β +
        (n : ℤ) • f4SimplyConnectedRootDatum.root α) :
    n = 1 ∧ f4SimplyConnectedRootDatum.pairing β α = -1 ∧ f4Length γ = 1 := by
  let P := f4SimplyConnectedRootDatum
  have hsym : 2 * P.pairing β α = P.pairing α β := by
    have hs := f4Length_mul_pairing_comm α β
    rw [hα, hβ, one_mul] at hs
    simpa only [P] using hs
  have hbdd : |P.pairing α β| ≤ 2 := by
    simpa only [P] using abs_pairing_f4SimplyConnectedRootDatum_le_two α β
  have hp : P.pairing β α ∈ ({-1, 0, 1} : Set ℤ) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    have hb := abs_le.mp hbdd
    omega
  have hlen := f4Length_of_root_eq_add_zsmul α β γ n h
  have hn' : (1 : ℤ) ≤ n := by exact_mod_cast hn
  have hnle : n ≤ 1 := by
    rcases f4Length_eq_one_or_eq_two γ with hγ | hγ <;>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp <;>
      rcases hp with hp | hp | hp <;>
      rw [hα, hβ, hγ, hp] at hlen <;>
      norm_num at hlen <;>
      nlinarith [sq_nonneg ((n : ℤ) - 1)]
  have hn_eq : n = 1 := by omega
  subst n
  have hp' : P.pairing β α ∈ ({-1, 0, 1} : Set ℤ) := by simpa only [P] using hp
  have hlen' := f4Length_of_root_eq_add_zsmul α β γ 1 (by simpa using h)
  constructor
  · rfl
  rcases f4Length_eq_one_or_eq_two γ with hγ | hγ
  · rw [hα, hβ, hγ] at hlen'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp'
    rcases hp' with hp' | hp' | hp'
    · exact ⟨hp', hγ⟩
    · rw [hp'] at hlen'
      norm_num at hlen'
    · rw [hp'] at hlen'
      norm_num at hlen'
  · rw [hα, hβ, hγ] at hlen'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp'
    rcases hp' with hp' | hp' | hp' <;> rw [hp'] at hlen' <;> norm_num at hlen'

/-- The short-short-to-long root edge has descending chain coefficient one,
so its Chevalley bracket coefficient has absolute value two. -/
theorem f4_chainBotCoeff_eq_one_of_short_add_short_eq_long (α β γ : Fin 48)
    (hα : f4Length α = 1) (hβ : f4Length β = 1) (hγ : f4Length γ = 2)
    (h : f4SimplyConnectedRootDatum.root γ =
      f4SimplyConnectedRootDatum.root β + f4SimplyConnectedRootDatum.root α) :
    f4SimplyConnectedRootDatum.chainBotCoeff α β = 1 := by
  let P := f4SimplyConnectedRootDatum
  have hrange : P.root α + P.root β ∈ Set.range P.root := by
    refine ⟨γ, ?_⟩
    rw [h, add_comm]
  have hlin := P.linearIndependent_of_add_mem_range_root' hrange
  have htop_ge := P.one_le_chainTopCoeff_of_root_add_mem hrange
  have htop_le : P.chainTopCoeff α β ≤ 1 := by
    by_contra hnot
    have htwo : 2 ≤ P.chainTopCoeff α β := by omega
    have hrange2 := (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff hlin).2 htwo
    obtain ⟨δ, hδ⟩ := hrange2
    have hne : β ≠ α := by
      intro hab
      subst β
      have hbad := (LinearIndependent.pair_iff.mp hlin) 1 (-1) (by simp)
      norm_num at hbad
    have hneg : P.root β ≠ -P.root α := by
      intro hab
      have hbad := (LinearIndependent.pair_iff.mp hlin) 1 1 (by
        rw [one_smul, one_smul, hab, add_neg_cancel])
      norm_num at hbad
    exact f4_not_root_eq_short_add_nsmul_short_of_two_le α β δ 2 hα hβ
      (by simpa only [P] using hneg) (by omega)
      (by simpa only [P, natCast_zsmul] using hδ)
  have htop : P.chainTopCoeff α β = 1 := by omega
  have hp := f4_pairing_eq_zero_of_short_add_short_eq_long α β γ hα hβ hγ h
  have hpIn : P.pairingIn ℤ β α = 0 := by
    have halg := P.algebraMap_pairingIn ℤ β α
    have hp' : P.pairing β α = 0 := by simpa only [P] using hp
    simpa using halg.trans hp'
  have hdiff := P.chainBotCoeff_sub_chainTopCoeff hlin
  rw [htop] at hdiff
  norm_num at hdiff
  rw [hpIn] at hdiff
  omega

/-- If two steps in a short-root direction carry a long root to another root, the Cartan
pairings are `-2` and `-1`, and the endpoint is long. This is the root string underlying the
quadratic term in the characteristic-two special isogeny. -/
theorem f4_pairings_of_long_add_two_short (α β γ : Fin 48)
    (hα : f4Length α = 1) (hβ : f4Length β = 2)
    (h : f4SimplyConnectedRootDatum.root γ =
      f4SimplyConnectedRootDatum.root β + (2 : ℤ) • f4SimplyConnectedRootDatum.root α) :
    f4SimplyConnectedRootDatum.pairing β α = -2 ∧
      f4SimplyConnectedRootDatum.pairing α β = -1 ∧ f4Length γ = 2 := by
  let P := f4SimplyConnectedRootDatum
  have hbdd : |P.pairing β α| ≤ 2 := by
    simpa only [P] using abs_pairing_f4SimplyConnectedRootDatum_le_two β α
  have hlen := f4Length_of_root_eq_add_zsmul α β γ 2 h
  have hsym := f4Length_mul_pairing_comm α β
  rcases f4Length_eq_one_or_eq_two γ with hγ | hγ
  · rw [hα, hβ, hγ] at hlen
    rw [hα, hβ] at hsym
    norm_num at hlen hsym
    omega
  · rw [hα, hβ, hγ] at hlen
    rw [hα, hβ] at hsym
    norm_num at hlen hsym
    have hp0 : f4Root β ⬝ᵥ f4Coroot α = -2 := by nlinarith [hlen]
    have hp1 : f4Root α ⬝ᵥ f4Coroot β = -1 := by nlinarith [hsym, hp0]
    exact ⟨by simpa only [f4SimplyConnectedRootDatum_pairing] using hp0,
      by simpa only [f4SimplyConnectedRootDatum_pairing] using hp1, hγ⟩

/-- A long root and a short direction joined by a two-step root string have descending
coefficient zero and ascending coefficient two. The intermediate root is short, and its outgoing
bracket coefficient has absolute value two. -/
theorem exists_f4_short_midpoint_of_long_add_two_short (α β γ : Fin 48)
    (hα : f4Length α = 1) (hβ : f4Length β = 2)
    (h : f4SimplyConnectedRootDatum.root γ =
      f4SimplyConnectedRootDatum.root β + (2 : ℤ) • f4SimplyConnectedRootDatum.root α) :
    ∃ δ : Fin 48,
      f4SimplyConnectedRootDatum.root δ =
          f4SimplyConnectedRootDatum.root β + f4SimplyConnectedRootDatum.root α ∧
        f4Length δ = 1 ∧
        f4SimplyConnectedRootDatum.chainBotCoeff α β = 0 ∧
        f4SimplyConnectedRootDatum.chainTopCoeff α β = 2 ∧
        f4SimplyConnectedRootDatum.chainBotCoeff α δ = 1 ∧
        f4SimplyConnectedRootDatum.chainTopCoeff α δ = 1 := by
  let P := f4SimplyConnectedRootDatum
  obtain ⟨hp, hp', hγ⟩ := f4_pairings_of_long_add_two_short α β γ hα hβ h
  have hne : α ≠ β := by
    intro hab
    subst β
    omega
  have hneg : P.root α ≠ -P.root β := by
    intro hneg
    have hpairs := (P.pairing_neg_two_neg_two_iff α β).2 hneg
    have : P.pairing α β = -1 := by simpa only [P] using hp'
    omega
  have hlin : LinearIndependent ℤ ![P.root α, P.root β] :=
    RootPairing.IsReduced.linearIndependent P hne hneg
  have htop_ge : 2 ≤ P.chainTopCoeff α β := by
    rw [← P.root_add_nsmul_mem_range_iff_le_chainTopCoeff hlin]
    refine ⟨γ, ?_⟩
    have hcast : (2 : ℕ) • P.root α = (2 : ℤ) • P.root α := by norm_num
    rw [hcast]
    simpa only [P] using h
  have hpIn : P.pairingIn ℤ β α = -2 := by
    have halg := P.algebraMap_pairingIn ℤ β α
    have hp0 : P.pairing β α = -2 := by simpa only [P] using hp
    simpa using halg.trans hp0
  have hdiff := P.chainBotCoeff_sub_chainTopCoeff hlin
  have hsum : P.chainBotCoeff α β + P.chainTopCoeff α β ≤ 3 :=
    P.chainBotCoeff_add_chainTopCoeff_le_three
  have hbot : P.chainBotCoeff α β = 0 := by omega
  have htop : P.chainTopCoeff α β = 2 := by omega
  have hrange : P.root β + P.root α ∈ Set.range P.root := by
    have hrange' :=
      (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff (n := 1) hlin).2
        (by omega)
    simpa only [one_nsmul] using hrange'
  obtain ⟨δ, hδ⟩ := hrange
  have hδlen := f4Length_of_root_eq_add_zsmul α β δ 1 (by
    simpa only [P, one_zsmul] using hδ)
  have hδshort : f4Length δ = 1 := by
    rw [hα, hβ, hp] at hδlen
    norm_num at hδlen
    exact hδlen
  have hδbot := P.chainBotCoeff_of_add hlin hδ
  have hδtop := P.chainTopCoeff_of_add hlin hδ
  refine ⟨δ, hδ, hδshort, hbot, htop, ?_, ?_⟩
  · omega
  · omega

end TauCeti.DynkinType
