/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.LinearAlgebra.RootSystem.Base
public import TauCeti.Algebra.Lie.Weights.Dimension
public import TauCeti.Algebra.Lie.Weights.Root.IntegralLattice

/-!
# The root--simple-coroot basis of a Chevalley Lie lattice

For a base `b` of the root system, the Chevalley Lie lattice has the expected integral basis:
one Chevalley root vector for every nonzero root and one coroot for every member of `b.support`.
The index is therefore `H.root ⊕ b.support`.

This is the coordinate source for reducing a Chevalley lattice modulo a prime: root coordinates
and simple-coroot coordinates remain named after scalar extension.

## Main declarations

* `TauCeti.IsChevalleySystem.rootSimpleCorootBasis`: the corresponding integral basis, indexed by
  `H.root ⊕ b.support`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §25.2.
* M. Geck, *Lie algebras and Chevalley groups*, Cambridge Studies in Advanced Mathematics 165,
  §4.1.
-/

public section

namespace TauCeti

open LieAlgebra LieAlgebra.IsKilling LieModule Module

universe u v

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]
  {ω : LieEquiv K L L} {x : Weight K H L → L}

namespace IsChevalleySystem

variable (hx : IsChevalleySystem ω x) (b : (rootSystem H).Base)

include hx

/-- The root vectors and simple coroots, as elements of the Chevalley Lie lattice. -/
private noncomputable def rootSimpleCorootFamily :
    H.root ⊕ b.support → hx.chevalleyLieLattice
  | Sum.inl alpha =>
      ⟨x alpha, hx.rootVector_mem_chevalleyLieLattice alpha⟩
  | Sum.inr i =>
      ⟨(coroot (i : Weight K H L) : L), hx.coroot_mem_chevalleyLieLattice i⟩

@[simp] private theorem coe_rootSimpleCorootFamily_inl (alpha : H.root) :
    (hx.rootSimpleCorootFamily b (Sum.inl alpha) : L) = x alpha := by
  simp [rootSimpleCorootFamily]

@[simp] private theorem coe_rootSimpleCorootFamily_inr (i : b.support) :
    (hx.rootSimpleCorootFamily b (Sum.inr i) : L) =
      (coroot (i : Weight K H L) : L) := by
  simp [rootSimpleCorootFamily]

private theorem span_rootSimpleCorootFamily_eq_top :
    Submodule.span K (Set.range fun i : H.root ⊕ b.support =>
      (hx.rootSimpleCorootFamily b i : L)) = ⊤ := by
  apply top_unique
  rw [← hx.toIsSl2System.span_range_sup_toSubmodule_eq_top]
  apply sup_le
  · rw [Submodule.span_le]
    rintro _ ⟨alpha, rfl⟩
    by_cases halpha : alpha.IsNonZero
    · exact Submodule.subset_span ⟨Sum.inl ⟨alpha, by simpa⟩, rfl⟩
    · rw [hx.toIsSl2System.eq_zero_of_isZero alpha (not_not.mp halpha)]
      exact Submodule.zero_mem _
  · intro h hh
    let h' : H := ⟨h, hh⟩
    -- Expose the ambient value of the Cartan-subalgebra element before expanding it in the
    -- coweight basis.
    change (h' : L) ∈ _
    rw [← b.toCoweightBasis.sum_repr h']
    -- The coercion from the Cartan subalgebra is definitionally its inclusion linear map.
    change H.incl (∑ i, (b.toCoweightBasis.repr h') i • b.toCoweightBasis i) ∈ _
    rw [map_sum]
    exact Submodule.sum_mem _ fun i _ => by
      rw [map_smul]
      exact Submodule.smul_mem _ _ <| by
        have hi : (hx.rootSimpleCorootFamily b (Sum.inr i) : L) ∈
            Submodule.span K (Set.range fun j : H.root ⊕ b.support =>
              (hx.rootSimpleCorootFamily b j : L)) :=
          Submodule.subset_span
            (Set.mem_range_self (Sum.inr i : H.root ⊕ b.support))
        simpa using hi

private theorem linearIndependent_rootSimpleCorootFamily_ambient :
    LinearIndependent K (fun i : H.root ⊕ b.support =>
      (hx.rootSimpleCorootFamily b i : L)) :=
  linearIndependent_of_top_le_span_of_card_eq_finrank
    (by rw [hx.span_rootSimpleCorootFamily_eq_top b])
    (card_root_sum_support_eq_finrank H b)

private theorem span_rootSimpleCorootFamily_lattice_eq_top :
    Submodule.span ℤ (Set.range (hx.rootSimpleCorootFamily b)) = ⊤ := by
  let P := Submodule.span ℤ (Set.range (hx.rootSimpleCorootFamily b))
  let Q := P.map hx.chevalleyLieLattice.toSubmodule.subtype
  have hroot (alpha : Weight K H L) : x alpha ∈ Q := by
    by_cases halpha : alpha.IsNonZero
    · let a : H.root := ⟨alpha, by simpa⟩
      exact ⟨hx.rootSimpleCorootFamily b (Sum.inl a),
        Submodule.subset_span ⟨Sum.inl a, rfl⟩, rfl⟩
    · rw [hx.toIsSl2System.eq_zero_of_isZero alpha (not_not.mp halpha)]
      exact Submodule.zero_mem _
  have hcoroot (alpha : Weight K H L) : (coroot alpha : L) ∈ Q := by
    by_cases halpha : alpha.IsNonZero
    · let a : H.root := ⟨alpha, by simpa⟩
      have ha := b.coroot_mem_span_int a
      have hclaim : ∀ (y : H),
          y ∈ Submodule.span ℤ ((rootSystem H).coroot '' b.support) → (y : L) ∈ Q := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hy =>
            obtain ⟨i, hi, rfl⟩ := hy
            let j : b.support := ⟨i, hi⟩
            exact ⟨hx.rootSimpleCorootFamily b (Sum.inr j),
              Submodule.subset_span ⟨Sum.inr j, rfl⟩, rfl⟩
        | zero => exact Submodule.zero_mem _
        | add y z _ _ hy hz =>
            -- Expose the ambient sum represented by the subtype addition.
            change (y : L) + (z : L) ∈ Q
            exact Submodule.add_mem _ hy hz
        | smul n y _ hy =>
            -- Expose the ambient integer scalar action represented by the subtype action.
            change n • (y : L) ∈ Q
            exact Submodule.smul_mem _ n hy
      exact hclaim _ ha
    · rw [coroot_eq_zero_iff.2 (not_not.mp halpha)]
      exact Submodule.zero_mem _
  have hspan : rootCorootSpan x ≤ Q := by
    rw [rootCorootSpan_le_iff]
    exact ⟨hroot, hcoroot⟩
  apply top_unique
  intro z _
  have hzroot : (z : L) ∈ rootCorootSpan x :=
    hx.mem_chevalleyLieLattice_iff.1 z.property
  have hz : (z : L) ∈ Q := hspan hzroot
  obtain ⟨w, hw, hwz⟩ := hz
  have : w = z := Subtype.ext hwz
  simpa [P, this] using hw

/-- The integral basis of the Chevalley Lie lattice consisting of one root vector for every
nonzero root and the simple coroots belonging to `b`. -/
noncomputable def rootSimpleCorootBasis :
    Basis (H.root ⊕ b.support) ℤ hx.chevalleyLieLattice := by
  apply Basis.mk
  · apply LinearIndependent.of_comp hx.chevalleyLieLattice.toSubmodule.subtype
    exact (hx.linearIndependent_rootSimpleCorootFamily_ambient b).restrict_scalars' ℤ
  · rw [hx.span_rootSimpleCorootFamily_lattice_eq_top b]

@[simp] theorem coe_rootSimpleCorootBasis_inl (alpha : H.root) :
    (hx.rootSimpleCorootBasis b (Sum.inl alpha) : L) = x alpha := by
  rw [rootSimpleCorootBasis, Basis.mk_apply]
  exact hx.coe_rootSimpleCorootFamily_inl b alpha

@[simp] theorem coe_rootSimpleCorootBasis_inr (i : b.support) :
    (hx.rootSimpleCorootBasis b (Sum.inr i) : L) =
      (coroot (i : Weight K H L) : L) := by
  rw [rootSimpleCorootBasis, Basis.mk_apply]
  exact hx.coe_rootSimpleCorootFamily_inr b i

end IsChevalleySystem

end TauCeti
