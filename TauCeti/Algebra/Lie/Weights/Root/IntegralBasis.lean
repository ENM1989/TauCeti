/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Weights.Dimension
public import TauCeti.Algebra.Lie.Weights.Root.IntegralLattice

/-!
# The root--simple-coroot basis of an integral root--coroot lattice

For a base `b` of the root system, the integral root--coroot span of an `IsSl2System` has the
expected basis: one root vector for every nonzero root and one coroot for every member of
`b.support`. The index is therefore `H.root ⊕ b.support`. A Chevalley Lie lattice receives the
same basis through its canonical identification with the root--coroot span.

This is the coordinate source for reducing a Chevalley lattice modulo a prime: root coordinates
and simple-coroot coordinates remain named after scalar extension.

## Main declarations

* `TauCeti.IsSl2System.rootSimpleCorootBasis`: the corresponding basis of the root--coroot
  lattice, indexed by `H.root ⊕ b.support`.
* `TauCeti.IsChevalleySystem.rootSimpleCorootBasis`: the transported basis of the Chevalley Lie
  lattice.

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

namespace IsSl2System

variable (hx : IsSl2System x) (b : (rootSystem H).Base)

include hx

/-- The root vectors and simple coroots, as elements of the integral root--coroot span. -/
private noncomputable def rootSimpleCorootFamily :
    H.root ⊕ b.support → rootCorootSpan x
  | Sum.inl alpha =>
      ⟨x alpha, rootVector_mem_rootCorootSpan x alpha⟩
  | Sum.inr i =>
      ⟨(coroot (i : Weight K H L) : L), coroot_mem_rootCorootSpan x i⟩

omit hx in
@[simp] private theorem coe_rootSimpleCorootFamily_inl (alpha : H.root) :
    (rootSimpleCorootFamily (x := x) b (Sum.inl alpha) : L) = x alpha := by
  simp [rootSimpleCorootFamily]

omit hx in
@[simp] private theorem coe_rootSimpleCorootFamily_inr (i : b.support) :
    (rootSimpleCorootFamily (x := x) b (Sum.inr i) : L) =
      (coroot (i : Weight K H L) : L) := by
  simp [rootSimpleCorootFamily]

private theorem span_rootSimpleCorootFamily_eq_top :
    Submodule.span K (Set.range fun i : H.root ⊕ b.support =>
      (rootSimpleCorootFamily (x := x) b i : L)) = ⊤ := by
  apply top_unique
  rw [← hx.span_range_sup_toSubmodule_eq_top]
  apply sup_le
  · rw [Submodule.span_le]
    rintro _ ⟨alpha, rfl⟩
    by_cases halpha : alpha.IsNonZero
    · exact Submodule.subset_span ⟨Sum.inl ⟨alpha, by simpa⟩, rfl⟩
    · rw [hx.eq_zero_of_isZero alpha (not_not.mp halpha)]
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
        have hi : (rootSimpleCorootFamily (x := x) b (Sum.inr i) : L) ∈
            Submodule.span K (Set.range fun j : H.root ⊕ b.support =>
              (rootSimpleCorootFamily (x := x) b j : L)) :=
          Submodule.subset_span
            (Set.mem_range_self (Sum.inr i : H.root ⊕ b.support))
        simpa using hi

private theorem linearIndependent_rootSimpleCorootFamily_ambient :
    LinearIndependent K (fun i : H.root ⊕ b.support =>
      (rootSimpleCorootFamily (x := x) b i : L)) :=
  linearIndependent_of_top_le_span_of_card_eq_finrank
    (by rw [hx.span_rootSimpleCorootFamily_eq_top b])
    (card_root_sum_support_eq_finrank H b)

private theorem span_rootSimpleCorootFamily_lattice_eq_top :
    Submodule.span ℤ (Set.range (rootSimpleCorootFamily (x := x) b)) = ⊤ := by
  let P := Submodule.span ℤ (Set.range (rootSimpleCorootFamily (x := x) b))
  let Q := P.map (rootCorootSpan x).subtype
  have hroot (alpha : Weight K H L) : x alpha ∈ Q := by
    by_cases halpha : alpha.IsNonZero
    · let a : H.root := ⟨alpha, by simpa⟩
      exact ⟨rootSimpleCorootFamily (x := x) b (Sum.inl a),
        Submodule.subset_span ⟨Sum.inl a, rfl⟩, rfl⟩
    · rw [hx.eq_zero_of_isZero alpha (not_not.mp halpha)]
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
            exact ⟨rootSimpleCorootFamily (x := x) b (Sum.inr j),
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
  have hz : (z : L) ∈ Q := hspan z.property
  obtain ⟨w, hw, hwz⟩ := hz
  have : w = z := Subtype.ext hwz
  simpa [P, this] using hw

/-- The integral basis of the root--coroot span consisting of one root vector for every nonzero
root and the simple coroots belonging to `b`. -/
noncomputable def rootSimpleCorootBasis :
    Basis (H.root ⊕ b.support) ℤ (rootCorootSpan x) := by
  apply Basis.mk
  · apply LinearIndependent.of_comp (rootCorootSpan x).subtype
    exact (hx.linearIndependent_rootSimpleCorootFamily_ambient b).restrict_scalars' ℤ
  · rw [hx.span_rootSimpleCorootFamily_lattice_eq_top b]

@[simp] theorem coe_rootSimpleCorootBasis_inl (alpha : H.root) :
    (hx.rootSimpleCorootBasis b (Sum.inl alpha) : L) = x alpha := by
  rw [rootSimpleCorootBasis, Basis.mk_apply]
  exact coe_rootSimpleCorootFamily_inl (x := x) b alpha

@[simp] theorem coe_rootSimpleCorootBasis_inr (i : b.support) :
    (hx.rootSimpleCorootBasis b (Sum.inr i) : L) =
      (coroot (i : Weight K H L) : L) := by
  rw [rootSimpleCorootBasis, Basis.mk_apply]
  exact coe_rootSimpleCorootFamily_inr (x := x) b i

end IsSl2System

namespace IsChevalleySystem

variable (hx : IsChevalleySystem ω x) (b : (rootSystem H).Base)

/-- The root--simple-coroot basis of the Chevalley Lie lattice, transported from the canonical
basis of its underlying root--coroot span. -/
noncomputable def rootSimpleCorootBasis :
    Basis (H.root ⊕ b.support) ℤ hx.chevalleyLieLattice :=
  (hx.toIsSl2System.rootSimpleCorootBasis b).map
    (LinearEquiv.ofEq _ _ hx.chevalleyLieLattice_toSubmodule.symm)

@[simp] theorem coe_rootSimpleCorootBasis_inl (alpha : H.root) :
    (hx.rootSimpleCorootBasis b (Sum.inl alpha) : L) = x alpha := by
  rw [rootSimpleCorootBasis, Basis.map_apply]
  change ((hx.toIsSl2System.rootSimpleCorootBasis b (Sum.inl alpha) :
    rootCorootSpan x) : L) = x alpha
  exact hx.toIsSl2System.coe_rootSimpleCorootBasis_inl b alpha

@[simp] theorem coe_rootSimpleCorootBasis_inr (i : b.support) :
    (hx.rootSimpleCorootBasis b (Sum.inr i) : L) =
      (coroot (i : Weight K H L) : L) := by
  rw [rootSimpleCorootBasis, Basis.map_apply]
  change ((hx.toIsSl2System.rootSimpleCorootBasis b (Sum.inr i) :
    rootCorootSpan x) : L) = (coroot (i : Weight K H L) : L)
  exact hx.toIsSl2System.coe_rootSimpleCorootBasis_inr b i

end IsChevalleySystem

end TauCeti
