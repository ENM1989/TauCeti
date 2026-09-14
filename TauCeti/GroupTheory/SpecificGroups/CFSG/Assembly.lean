/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import TauCeti.GroupTheory.SimpleGroupUniverse
public import TauCeti.GroupTheory.SpecificGroups.CFSG.ReeF4.Basic
public import TauCeti.GroupTheory.SpecificGroups.CFSG.ReeG2.Basic
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Suzuki.Basic
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TrialityD4
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TwistedE6
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeA
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeB.Basic
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeD
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeE6
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeE7.Frobenius
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Unimodular

/-!
# The classification list assembled, and the statement of the classification

Every branch of the classification list has its own carrier, its own Steinberg endomorphism and
its own candidate group. This file collects them into one group-valued function on the index type
and states the classification against it.

For a valid Lie-type index the constructor selects the family: the seventeen constructors of
`TauCeti.LieTypeIndex` dispatch to the twelve validated subtypes that carry the per-family
constructions. The dispatch needs no case split on the rank or the field order inside a
constructor, every family being built uniformly in those parameters on one carrier. Two families
share a carrier with another branch and reach it through the named projection of their index:
`Dₙ(q)` and `²Dₙ(q)` through the type-`D` diagram index, and `²B₂(2^(2m+1))` through the rank-two
type-`B` index.

`TauCeti.CFSGIndex.Group` then adds the three non-Lie branches: the cyclic group of prime order as
`Multiplicative (ZMod p)`, the alternating group on `Fin n`, and the sporadic group defined by its
transcribed presentation. `TauCeti.ClassificationStatement` says that every finite simple group is
isomorphic to one of these, and `TauCeti.classificationStatement_of_zero` reduces the statement in
an arbitrary universe to the statement in `Type`.

Nothing here asserts that any candidate group is finite, perfect, or simple, nor that any explicit
carrier is the pinned simply connected Chevalley--Demazure group scheme of its diagram.

## Main declarations

* `TauCeti.ValidLieTypeIndex.AmbientGroup`, `TauCeti.ValidLieTypeIndex.steinberg`,
  `TauCeti.ValidLieTypeIndex.FixedPoints` and `TauCeti.ValidLieTypeIndex.Group`: the carrier, the
  Steinberg endomorphism, its fixed points and the candidate group of a valid Lie-type index.
* `TauCeti.CFSGIndex.Group`: the group named by an index of the classification list.
* `TauCeti.ClassificationStatement`: the statement of the classification.

## Main results

* `TauCeti.ValidLieTypeIndex.group_eq_fixedPointCandidate`: the candidate group of a valid
  Lie-type index is the derived subgroup of the fixed points of its Steinberg endomorphism,
  modulo the centre of that derived subgroup, on every branch.
* `TauCeti.classificationStatement_of_zero`: the classification in `Type` implies the
  classification in every universe.

## References

* R. W. Carter, *Simple Groups of Lie Type*, for the fixed-point constructions.
* D. Gorenstein, R. Lyons, and R. Solomon, *The Classification of the Finite Simple Groups*, for
  the conventional list.
-/

public section

namespace TauCeti

noncomputable section

/-! ## The uniform Lie-type branch -/

/-- **The ambient group of a valid Lie-type index**: the group of algebraic-closure-valued points
of the carrier its family is built on, selected by the constructor the index carries. -/
abbrev ValidLieTypeIndex.AmbientGroup (d : ValidLieTypeIndex) : Type :=
  -- Matching on `d.1` rather than destructuring `d` keeps `d` itself a variable, which is what
  -- lets each branch hand the whole validated index to its family's subtype.
  match h : d.1 with
  | .A _ _ => TypeALieIndex.AmbientGroup ⟨d, (LieTypeIndex.isTypeA_iff _).mpr (h ▸ trivial)⟩
  | .twistedA _ _ =>
      TypeALieIndex.AmbientGroup ⟨d, (LieTypeIndex.isTypeA_iff _).mpr (h ▸ trivial)⟩
  | .B _ _ => TypeBLieIndex.AmbientGroup ⟨d, h ▸ trivial⟩
  | .C _ _ => TypeCLieIndex.AmbientGroup ⟨d, h ▸ trivial⟩
  | .D _ _ =>
      TypeDDiagramLieIndex.AmbientGroup (TypeDLieIndex.toTypeDDiagramLieIndex
        ⟨d, (LieTypeIndex.isTypeD_iff _).mpr (h ▸ trivial)⟩)
  | .twistedD _ _ =>
      TypeDDiagramLieIndex.AmbientGroup (TypeTwistedDLieIndex.toTypeDDiagramLieIndex
        ⟨d, (LieTypeIndex.isTypeTwistedD_iff _).mpr (h ▸ trivial)⟩)
  | .E6 _ => TypeE6LieIndex.AmbientGroup ⟨d, (LieTypeIndex.isTypeE6_iff _).mpr (h ▸ trivial)⟩
  | .E7 _ => TypeE7LieIndex.AmbientGroup ⟨d, (LieTypeIndex.isTypeE7_iff _).mpr (h ▸ trivial)⟩
  | .E8 _ =>
      UnimodularExceptionalIndex.AmbientGroup
        ⟨⟨d, (LieTypeIndex.hasUnimodularDiagram_iff _).mpr (h ▸ trivial)⟩,
          (LieTypeIndex.usesHalfFrobenius_iff d.1).not.mpr (h ▸ not_false)⟩
  | .F4 _ =>
      UnimodularExceptionalIndex.AmbientGroup
        ⟨⟨d, (LieTypeIndex.hasUnimodularDiagram_iff _).mpr (h ▸ trivial)⟩,
          (LieTypeIndex.usesHalfFrobenius_iff d.1).not.mpr (h ▸ not_false)⟩
  | .G2 _ =>
      UnimodularExceptionalIndex.AmbientGroup
        ⟨⟨d, (LieTypeIndex.hasUnimodularDiagram_iff _).mpr (h ▸ trivial)⟩,
          (LieTypeIndex.usesHalfFrobenius_iff d.1).not.mpr (h ▸ not_false)⟩
  | .twistedE6 _ =>
      TypeTwistedE6LieIndex.AmbientGroup ⟨d, (LieTypeIndex.isTypeTwistedE6_iff _).mpr (h ▸ trivial)⟩
  | .trialityD4 _ =>
      TypeTrialityD4LieIndex.AmbientGroup
        ⟨d, (LieTypeIndex.isTypeTrialityD4_iff _).mpr (h ▸ trivial)⟩
  | .suzuki _ =>
      RankTwoBLieIndex.AmbientGroup (SuzukiLieIndex.toRankTwoBLieIndex
        ⟨d, (LieTypeIndex.isSuzuki_iff _).mpr (h ▸ trivial)⟩)
  | .reeG2 _ => ReeG2LieIndex.AmbientGroup ⟨d, (LieTypeIndex.isReeG2_iff _).mpr (h ▸ trivial)⟩
  | .reeF4 _ => ReeF4LieIndex.AmbientGroup ⟨d, (LieTypeIndex.isReeF4_iff _).mpr (h ▸ trivial)⟩
  | .tits => ReeF4LieIndex.AmbientGroup ⟨d, (LieTypeIndex.isReeF4_iff _).mpr (h ▸ trivial)⟩

instance (d : ValidLieTypeIndex) : _root_.Group d.AmbientGroup := by
  unfold ValidLieTypeIndex.AmbientGroup
  split <;> infer_instance

/-- **The Steinberg endomorphism of a valid Lie-type index**: the endomorphism of its ambient
group whose fixed points the classification recipe is run on, selected by the constructor the
index carries. On an untwisted family it is the `q`-power Frobenius, on a graph-twisted family the
graph automorphism composed with that Frobenius, and on a Suzuki--Ree family an odd power of a
half-Frobenius. -/
def ValidLieTypeIndex.steinberg :
    (d : ValidLieTypeIndex) → (d.AmbientGroup →* d.AmbientGroup)
  -- Here the index is destructured rather than matched on through `d.1`, so that the ambient
  -- group in the expected type reduces to the branch's own carrier.
  | ⟨.A r q, hv⟩ => TypeALieIndex.steinberg ⟨⟨.A r q, hv⟩, (LieTypeIndex.isTypeA_iff _).mpr trivial⟩
  | ⟨.twistedA r q, hv⟩ =>
      TypeALieIndex.steinberg ⟨⟨.twistedA r q, hv⟩, (LieTypeIndex.isTypeA_iff _).mpr trivial⟩
  | ⟨.B r q, hv⟩ =>
      TypeBLieIndex.steinberg ⟨⟨.B r q, hv⟩, trivial⟩
  | ⟨.C r q, hv⟩ =>
      TypeCLieIndex.steinberg ⟨⟨.C r q, hv⟩, trivial⟩
  | ⟨.D r q, hv⟩ =>
      TypeDLieIndex.steinberg ⟨⟨.D r q, hv⟩, (LieTypeIndex.isTypeD_iff _).mpr trivial⟩
  | ⟨.twistedD r q, hv⟩ =>
      TypeTwistedDLieIndex.steinberg
        ⟨⟨.twistedD r q, hv⟩, (LieTypeIndex.isTypeTwistedD_iff _).mpr trivial⟩
  | ⟨.E6 q, hv⟩ =>
      TypeE6LieIndex.steinberg ⟨⟨.E6 q, hv⟩, (LieTypeIndex.isTypeE6_iff _).mpr trivial⟩
  | ⟨.E7 q, hv⟩ =>
      TypeE7LieIndex.steinberg ⟨⟨.E7 q, hv⟩, (LieTypeIndex.isTypeE7_iff _).mpr trivial⟩
  | ⟨.E8 q, hv⟩ =>
      UnimodularExceptionalIndex.steinberg
        ⟨⟨⟨.E8 q, hv⟩, (LieTypeIndex.hasUnimodularDiagram_iff _).mpr trivial⟩,
          (LieTypeIndex.usesHalfFrobenius_iff _).not.mpr not_false⟩
  | ⟨.F4 q, hv⟩ =>
      UnimodularExceptionalIndex.steinberg
        ⟨⟨⟨.F4 q, hv⟩, (LieTypeIndex.hasUnimodularDiagram_iff _).mpr trivial⟩,
          (LieTypeIndex.usesHalfFrobenius_iff _).not.mpr not_false⟩
  | ⟨.G2 q, hv⟩ =>
      UnimodularExceptionalIndex.steinberg
        ⟨⟨⟨.G2 q, hv⟩, (LieTypeIndex.hasUnimodularDiagram_iff _).mpr trivial⟩,
          (LieTypeIndex.usesHalfFrobenius_iff _).not.mpr not_false⟩
  | ⟨.twistedE6 q, hv⟩ =>
      TypeTwistedE6LieIndex.steinberg
        ⟨⟨.twistedE6 q, hv⟩, (LieTypeIndex.isTypeTwistedE6_iff _).mpr trivial⟩
  | ⟨.trialityD4 q, hv⟩ =>
      TypeTrialityD4LieIndex.steinberg
        ⟨⟨.trialityD4 q, hv⟩, (LieTypeIndex.isTypeTrialityD4_iff _).mpr trivial⟩
  | ⟨.suzuki m, hv⟩ =>
      SuzukiLieIndex.steinberg ⟨⟨.suzuki m, hv⟩, (LieTypeIndex.isSuzuki_iff _).mpr trivial⟩
  | ⟨.reeG2 m, hv⟩ =>
      ReeG2LieIndex.steinberg ⟨⟨.reeG2 m, hv⟩, (LieTypeIndex.isReeG2_iff _).mpr trivial⟩
  | ⟨.reeF4 m, hv⟩ =>
      ReeF4LieIndex.steinberg ⟨⟨.reeF4 m, hv⟩, (LieTypeIndex.isReeF4_iff _).mpr trivial⟩
  | ⟨.tits, hv⟩ =>
      ReeF4LieIndex.steinberg ⟨⟨.tits, hv⟩, (LieTypeIndex.isReeF4_iff _).mpr trivial⟩

/-- The fixed subgroup of the Steinberg endomorphism of a valid Lie-type index. -/
abbrev ValidLieTypeIndex.FixedPoints (d : ValidLieTypeIndex) : Type :=
  ↥(fixedSubgroup d.steinberg)

/-- **The finite-simple-group candidate attached to a valid Lie-type index**: the derived subgroup
of the Steinberg fixed points, modulo the centre of that derived subgroup. No finiteness or
simplicity assertion is part of this definition, and no explicit carrier is identified with the
pinned simply connected group scheme of its diagram. -/
abbrev ValidLieTypeIndex.Group (d : ValidLieTypeIndex) : Type :=
  match h : d.1 with
  | .A _ _ => TypeALieIndex.Group ⟨d, (LieTypeIndex.isTypeA_iff _).mpr (h ▸ trivial)⟩
  | .twistedA _ _ => TypeALieIndex.Group ⟨d, (LieTypeIndex.isTypeA_iff _).mpr (h ▸ trivial)⟩
  | .B _ _ => TypeBLieIndex.Group ⟨d, h ▸ trivial⟩
  | .C _ _ => TypeCLieIndex.Group ⟨d, h ▸ trivial⟩
  | .D _ _ => TypeDLieIndex.Group ⟨d, (LieTypeIndex.isTypeD_iff _).mpr (h ▸ trivial)⟩
  | .twistedD _ _ =>
      TypeTwistedDLieIndex.Group ⟨d, (LieTypeIndex.isTypeTwistedD_iff _).mpr (h ▸ trivial)⟩
  | .E6 _ => TypeE6LieIndex.Group ⟨d, (LieTypeIndex.isTypeE6_iff _).mpr (h ▸ trivial)⟩
  | .E7 _ => TypeE7LieIndex.Group ⟨d, (LieTypeIndex.isTypeE7_iff _).mpr (h ▸ trivial)⟩
  | .E8 _ =>
      UnimodularExceptionalIndex.Group
        ⟨⟨d, (LieTypeIndex.hasUnimodularDiagram_iff _).mpr (h ▸ trivial)⟩,
          (LieTypeIndex.usesHalfFrobenius_iff d.1).not.mpr (h ▸ not_false)⟩
  | .F4 _ =>
      UnimodularExceptionalIndex.Group
        ⟨⟨d, (LieTypeIndex.hasUnimodularDiagram_iff _).mpr (h ▸ trivial)⟩,
          (LieTypeIndex.usesHalfFrobenius_iff d.1).not.mpr (h ▸ not_false)⟩
  | .G2 _ =>
      UnimodularExceptionalIndex.Group
        ⟨⟨d, (LieTypeIndex.hasUnimodularDiagram_iff _).mpr (h ▸ trivial)⟩,
          (LieTypeIndex.usesHalfFrobenius_iff d.1).not.mpr (h ▸ not_false)⟩
  | .twistedE6 _ =>
      TypeTwistedE6LieIndex.Group ⟨d, (LieTypeIndex.isTypeTwistedE6_iff _).mpr (h ▸ trivial)⟩
  | .trialityD4 _ =>
      TypeTrialityD4LieIndex.Group ⟨d, (LieTypeIndex.isTypeTrialityD4_iff _).mpr (h ▸ trivial)⟩
  | .suzuki _ => SuzukiLieIndex.Group ⟨d, (LieTypeIndex.isSuzuki_iff _).mpr (h ▸ trivial)⟩
  | .reeG2 _ => ReeG2LieIndex.Group ⟨d, (LieTypeIndex.isReeG2_iff _).mpr (h ▸ trivial)⟩
  | .reeF4 _ => ReeF4LieIndex.Group ⟨d, (LieTypeIndex.isReeF4_iff _).mpr (h ▸ trivial)⟩
  | .tits => ReeF4LieIndex.Group ⟨d, (LieTypeIndex.isReeF4_iff _).mpr (h ▸ trivial)⟩

/-- The candidate group of a valid Lie-type index is a group, being on every branch a quotient of
a subgroup of the points of that branch's carrier. -/
instance (d : ValidLieTypeIndex) : _root_.Group d.Group := by
  unfold ValidLieTypeIndex.Group
  split <;> infer_instance

/-- **The candidate group of a valid Lie-type index is the fixed-point recipe run on its Steinberg
endomorphism**, on every one of the seventeen branches. -/
theorem ValidLieTypeIndex.group_eq_fixedPointCandidate (d : ValidLieTypeIndex) :
    d.Group = FixedPointCandidate d.steinberg := by
  obtain ⟨d, hd⟩ := d
  cases d <;> rfl

/-! ## The classification list -/

/-- **The group named by an index of the classification list**: the cyclic group of prime order,
the alternating group on a finite type, the candidate group of a valid Lie-type index, or the
group presented by a sporadic name's transcribed presentation. -/
abbrev CFSGIndex.Group : CFSGIndex → Type
  | .cyclic p _ => Multiplicative (ZMod p)
  | .alternating degree _ => alternatingGroup (Fin degree)
  | .lie index => index.Group
  | .sporadic name => name.Group

/-- Each of the four branches of the classification list names a group. -/
instance (i : CFSGIndex) : _root_.Group i.Group := by
  cases i <;> infer_instance

universe u

/-- **Classification of finite simple groups, statement only.** Every finite simple group is
isomorphic to the group named by some index of the classification list. The existential is over
the index: the validity conditions pick conventional representatives, but no uniqueness of the
index is asserted, and no group named by an index is asserted to be finite or simple. -/
def ClassificationStatement : Prop :=
  ∀ (G : Type u) [_root_.Group G] [Finite G] [IsSimpleGroup G],
    ∃ i : CFSGIndex, Nonempty (G ≃* i.Group)

/-- **The classification in `Type` implies the classification in every universe.** A finite group
is equivalent to one with carrier in `Type`, and its group and simplicity structure transport
along that equivalence, so the statement in universe zero is the substantive one. -/
theorem classificationStatement_of_zero (h : ClassificationStatement.{0}) :
    ClassificationStatement.{u} :=
  fun G _ _ _ =>
    exists_mulEquiv_of_forall_finite_isSimpleGroup_zero CFSGIndex.Group (fun H _ _ _ => h H) G

end

end TauCeti
