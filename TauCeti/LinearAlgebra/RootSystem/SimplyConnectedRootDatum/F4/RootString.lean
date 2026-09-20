/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.F4.Length
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.F4.ShortRootWeight.Basic
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
    f4SimplyConnectedRootDatum.pairing β α ∈ ({-1, 0, 1} : Set ℤ) :=
  f4SimplyConnectedRootDatum.pairing_mem_neg_one_zero_one_of_short f4Length
    f4Length_mul_pairing_comm α β (abs_pairing_f4SimplyConnectedRootDatum_le_two β α)
    hα hβ hne hneg

/-- A root string through two distinct, non-opposite short F4 roots has no term
two or more steps in the positive direction. -/
theorem f4_not_root_eq_short_add_nsmul_short_of_two_le (α β γ : Fin 48) (n : ℕ)
    (hα : f4Length α = 1) (hβ : f4Length β = 1)
    (hneg : f4SimplyConnectedRootDatum.root β ≠
      -f4SimplyConnectedRootDatum.root α) (hn : 2 ≤ n)
    (h : f4SimplyConnectedRootDatum.root γ =
      f4SimplyConnectedRootDatum.root β +
        (n : ℤ) • f4SimplyConnectedRootDatum.root α) : False :=
  f4SimplyConnectedRootDatum.not_root_eq_short_add_nsmul_short_of_two_le f4Length
    f4Length_mul_pairing_comm α β γ n (abs_pairing_f4SimplyConnectedRootDatum_le_two β α)
    hα hβ (f4Length_eq_one_or_eq_two γ) hneg hn h

/-- When the sum of two short F4 roots is long, their Cartan pairing is zero. -/
theorem f4_pairing_eq_zero_of_short_add_short_eq_long (α β γ : Fin 48)
    (hα : f4Length α = 1) (hβ : f4Length β = 1) (hγ : f4Length γ = 2)
    (h : f4SimplyConnectedRootDatum.root γ =
      f4SimplyConnectedRootDatum.root β + f4SimplyConnectedRootDatum.root α) :
    f4SimplyConnectedRootDatum.pairing β α = 0 :=
  f4SimplyConnectedRootDatum.pairing_eq_zero_of_short_add_short_eq_long f4Length
    f4Length_mul_pairing_comm α β γ hα hβ hγ h

/-- A positive root string from a short root in a long-root direction has at most
one step, and that step is again short. -/
theorem f4_n_eq_one_and_pairing_eq_neg_one_and_length_eq_one_of_short_add_nsmul_long
    (α β γ : Fin 48) (n : ℕ)
    (hα : f4Length α = 2) (hβ : f4Length β = 1) (hn : 0 < n)
    (h : f4SimplyConnectedRootDatum.root γ =
      f4SimplyConnectedRootDatum.root β +
        (n : ℤ) • f4SimplyConnectedRootDatum.root α) :
    n = 1 ∧ f4SimplyConnectedRootDatum.pairing β α = -1 ∧ f4Length γ = 1 :=
  RootPairing.n_eq_one_and_pairing_eq_neg_one_and_length_eq_one_of_short_add_nsmul_long
    (P := f4SimplyConnectedRootDatum) f4Length f4Length_mul_pairing_comm
    α β γ n (abs_pairing_f4SimplyConnectedRootDatum_le_two α β)
    hα hβ (f4Length_eq_one_or_eq_two γ) hn h

/-- The short-short-to-long root edge has descending chain coefficient one,
so its Chevalley bracket coefficient has absolute value two. -/
theorem f4_chainBotCoeff_eq_one_of_short_add_short_eq_long (α β γ : Fin 48)
    (hα : f4Length α = 1) (hβ : f4Length β = 1) (hγ : f4Length γ = 2)
    (h : f4SimplyConnectedRootDatum.root γ =
      f4SimplyConnectedRootDatum.root β + f4SimplyConnectedRootDatum.root α) :
    f4SimplyConnectedRootDatum.chainBotCoeff α β = 1 :=
  f4SimplyConnectedRootDatum.chainBotCoeff_eq_one_of_short_add_short_eq_long f4Length
    f4Length_mul_pairing_comm α β γ (fun δ _ => f4Length_eq_one_or_eq_two δ)
    hα hβ hγ h

/-- If two steps in a short-root direction carry a long root to another root, the Cartan
pairings are `-2` and `-1`, and the endpoint is long. This is the root string underlying the
quadratic term in the characteristic-two special isogeny. -/
theorem f4_pairings_of_long_add_two_short (α β γ : Fin 48)
    (hα : f4Length α = 1) (hβ : f4Length β = 2)
    (h : f4SimplyConnectedRootDatum.root γ =
      f4SimplyConnectedRootDatum.root β + (2 : ℤ) • f4SimplyConnectedRootDatum.root α) :
    f4SimplyConnectedRootDatum.pairing β α = -2 ∧
      f4SimplyConnectedRootDatum.pairing α β = -1 ∧ f4Length γ = 2 :=
  f4SimplyConnectedRootDatum.pairings_of_long_add_two_short f4Length
    f4Length_mul_pairing_comm α β γ hα hβ (f4Length_eq_one_or_eq_two γ) h

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
        f4SimplyConnectedRootDatum.chainTopCoeff α δ = 1 :=
  f4SimplyConnectedRootDatum.exists_short_midpoint_of_long_add_two_short f4Length
    f4Length_mul_pairing_comm α β γ hα hβ (f4Length_eq_one_or_eq_two γ) h

/-- A root edge whose source and target are both short has descending chain coefficient zero,
regardless of the length of the root direction. -/
theorem f4_chainBotCoeff_eq_zero_of_add_eq_short (α β γ : Fin 48)
    (hβ : f4Length β = 1) (hγ : f4Length γ = 1)
    (h : f4SimplyConnectedRootDatum.root γ =
      f4SimplyConnectedRootDatum.root β + f4SimplyConnectedRootDatum.root α) :
    f4SimplyConnectedRootDatum.chainBotCoeff α β = 0 :=
  f4SimplyConnectedRootDatum.chainBotCoeff_eq_zero_of_add_eq_short f4Length
    f4Length_mul_pairing_comm α β γ f4Length_eq_one_or_eq_two hβ hγ h

/-- Every long F₄ root has a short neighbour one step away in a descending-free root string.
Concretely, for a long root `α` there is a short root `β` with `⟨β, α∨⟩ = -1`; then `β + α`
is a short root and the root string through `β` in the `α` direction has bottom coefficient zero.
The proof uses that the short roots span the character lattice, without enumerating roots. -/
theorem exists_f4_short_neighbor_of_long (α : Fin 48) (hα : f4Length α = 2) :
    ∃ β γ : Fin 48,
      f4Length β = 1 ∧
      f4SimplyConnectedRootDatum.pairing β α = -1 ∧
      f4SimplyConnectedRootDatum.root γ =
        f4SimplyConnectedRootDatum.root β + f4SimplyConnectedRootDatum.root α ∧
      f4Length γ = 1 ∧
      f4SimplyConnectedRootDatum.chainBotCoeff α β = 0 := by
  let P := f4SimplyConnectedRootDatum
  have hexists : ∃ β : Fin 48, f4Length β = 1 ∧ P.pairing β α ≠ 0 := by
    by_contra h
    push Not at h
    have hzero : ∀ x ∈ Submodule.span ℤ (Set.range f4ShortRootWeight),
        P.toLinearMap x (P.coroot α) = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
          obtain ⟨a, rfl⟩ := hx
          by_cases ha : f4ShortRootWeight a = 0
          · simp [ha]
          · obtain ⟨β, hβ, hroot⟩ :=
              (f4ShortRootWeight_ne_zero_iff_exists_shortRoot a).mp ha
            have hroot' : P.root β = f4ShortRootWeight a := by
              simpa only [P, f4SimplyConnectedRootDatum_root] using hroot
            rw [← hroot', P.root_coroot_eq_pairing, h β hβ]
      | zero => simp
      | add x y hx hy ihx ihy => simp [ihx, ihy]
      | smul a x hx ih =>
          simp only [map_smul, LinearMap.smul_apply, ih, smul_zero]
    have hmem : P.root α ∈ Submodule.span ℤ (Set.range f4ShortRootWeight) := by
      rw [span_range_f4ShortRootWeight_eq_top]
      exact Submodule.mem_top
    have hbad := hzero (P.root α) hmem
    rw [P.root_coroot_eq_pairing, P.pairing_same] at hbad
    norm_num at hbad
  obtain ⟨β₀, hβ₀, hp₀_ne⟩ := hexists
  have hsym := f4Length_mul_pairing_comm α β₀
  rw [hα, hβ₀] at hsym
  simp only [one_mul] at hsym
  change 2 * P.pairing β₀ α = P.pairing α β₀ at hsym
  have hbound := abs_pairing_f4SimplyConnectedRootDatum_le_two α β₀
  have hp₀ : P.pairing β₀ α = -1 ∨ P.pairing β₀ α = 1 := by
    change |P.pairing α β₀| ≤ 2 at hbound
    have hb := abs_le.mp hbound
    omega
  obtain ⟨β, hβ, hp⟩ : ∃ β : Fin 48, f4Length β = 1 ∧ P.pairing β α = -1 := by
    rcases hp₀ with hp₀ | hp₀
    · exact ⟨β₀, hβ₀, hp₀⟩
    · let β := P.reflectionPerm β₀ β₀
      have hβroot : P.root β = P.root β₀ + (-2 : ℤ) • P.root β₀ := by
        rw [P.root_reflectionPerm, P.reflection_apply_self]
        module
      have hβlen := f4Length_of_root_eq_add_zsmul β₀ β₀ β (-2) hβroot
      have hβ : f4Length β = 1 := by
        rw [hβ₀, P.pairing_same] at hβlen
        norm_num at hβlen
        exact hβlen
      have hβpair : P.pairing β α = -1 := by
        change P.pairing (P.reflectionPerm β₀ β₀) α = -1
        rw [P.pairing_reflectionPerm_self_left, hp₀]
      exact ⟨β, hβ, hβpair⟩
  let γ := P.reflectionPerm α β
  have hγroot : P.root γ = P.root β + P.root α := by
    rw [← P.reflectionPerm_root, P.root_coroot_eq_pairing, hp]
    module
  have hγroot' : f4Root γ = f4Root β + f4Root α := by
    simpa only [P, f4SimplyConnectedRootDatum_root] using hγroot
  have hγlen := f4Length_of_root_eq_add_zsmul α β γ 1 (by simpa using hγroot')
  have hγ : f4Length γ = 1 := by
    rw [hα, hβ, hp] at hγlen
    norm_num at hγlen
    exact hγlen
  have hbot : P.chainBotCoeff α β = 0 := by
    rw [P.chainBotCoeff_eq_zero_iff]
    right
    rintro ⟨δ, hδ⟩
    have hδ' : f4Root δ = f4Root β - f4Root α := by
      simpa only [P, f4SimplyConnectedRootDatum_root] using hδ
    have hδlen := f4Length_of_root_eq_add_zsmul α β δ (-1) (by
      simpa [sub_eq_add_neg] using hδ')
    rw [hα, hβ, hp] at hδlen
    norm_num at hδlen
    rcases f4Length_eq_one_or_eq_two δ with hδ | hδ <;> omega
  exact ⟨β, γ, hβ, hp, hγroot, hγ, hbot⟩

/-- A short root with Cartan pairing one has no positive step in the given root direction. -/
theorem f4_chainTopCoeff_eq_zero_of_short_pairing_eq_one (α β : Fin 48)
    (hβ : f4Length β = 1)
    (hpair : f4SimplyConnectedRootDatum.pairing β α = 1) :
    f4SimplyConnectedRootDatum.chainTopCoeff α β = 0 := by
  let P := f4SimplyConnectedRootDatum
  rw [P.chainTopCoeff_eq_zero_iff]
  right
  rintro ⟨γ, hγ⟩
  have hlen := f4Length_of_root_eq_add_zsmul α β γ 1 (by
    simpa only [P, one_zsmul] using hγ)
  rcases f4Length_eq_one_or_eq_two α with hα | hα <;>
    rcases f4Length_eq_one_or_eq_two γ with hγlen | hγlen <;>
    rw [hα, hβ, hγlen, hpair] at hlen <;> norm_num at hlen

/-- A short root orthogonal to a long root has no positive step in the long-root direction. -/
theorem f4_chainTopCoeff_eq_zero_of_short_long_pairing_eq_zero (α β : Fin 48)
    (hα : f4Length α = 2) (hβ : f4Length β = 1)
    (hpair : f4SimplyConnectedRootDatum.pairing β α = 0) :
    f4SimplyConnectedRootDatum.chainTopCoeff α β = 0 := by
  let P := f4SimplyConnectedRootDatum
  rw [P.chainTopCoeff_eq_zero_iff]
  right
  rintro ⟨γ, hγ⟩
  have hlen := f4Length_of_root_eq_add_zsmul α β γ 1 (by
    simpa only [P, one_zsmul] using hγ)
  rcases f4Length_eq_one_or_eq_two γ with hγlen | hγlen <;>
    rw [hα, hβ, hγlen, hpair] at hlen <;> norm_num at hlen

end TauCeti.DynkinType
