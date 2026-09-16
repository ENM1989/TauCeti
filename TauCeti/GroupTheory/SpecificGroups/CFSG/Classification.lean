/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The statement of the classification of finite simple groups

This file assembles the explicit cyclic, alternating, Lie-type, and sporadic carriers indexed by
`TauCeti.CFSGIndex`. It then records the classification as a named proposition. No finiteness or
simplicity property of a listed carrier is asserted here, and the classification proposition is
not proved.

## Main definitions

* `TauCeti.ValidLieTypeIndex.Group`: the concrete fixed-point, derived-subgroup, central-quotient
  carrier selected by a valid Lie-type index.
* `TauCeti.CFSGIndex.Group`: the concrete carrier selected by an index on the classification list.
* `TauCeti.ClassificationStatement`: every finite simple group is isomorphic to a listed carrier.
* `TauCeti.classificationStatement_of_zero`: the universe-zero statement implies the statement in
  every universe.

## Roadmap

This is milestone A0 of `TauCetiRoadmap/CFSGStatement/README.md`.
-/

public section

namespace TauCeti

/-- The concrete group represented by a valid Lie-type index. -/
abbrev ValidLieTypeIndex.Group (d : ValidLieTypeIndex) : Type :=
  match d with
  | ⟨.A rank q, h⟩ => TypeALieIndex.Group ⟨⟨.A rank q, h⟩, by simp⟩
  | ⟨.twistedA rank q, h⟩ => TypeALieIndex.Group ⟨⟨.twistedA rank q, h⟩, by simp⟩
  | ⟨.B rank q, h⟩ => TypeBLieIndex.Group ⟨⟨.B rank q, h⟩, trivial⟩
  | ⟨.C rank q, h⟩ => TypeCLieIndex.Group ⟨⟨.C rank q, h⟩, trivial⟩
  | ⟨.D rank q, h⟩ => TypeDLieIndex.Group ⟨⟨.D rank q, h⟩, by simp⟩
  | ⟨.twistedD rank q, h⟩ =>
      TypeTwistedDLieIndex.Group ⟨⟨.twistedD rank q, h⟩, by simp⟩
  | ⟨.E6 q, h⟩ => TypeE6LieIndex.Group ⟨⟨.E6 q, h⟩, by simp⟩
  | ⟨.E7 q, h⟩ => TypeE7LieIndex.Group ⟨⟨.E7 q, h⟩, by simp⟩
  | ⟨.E8 q, h⟩ =>
      UnimodularExceptionalIndex.Group ⟨⟨⟨.E8 q, h⟩, by simp⟩, by simp⟩
  | ⟨.F4 q, h⟩ =>
      UnimodularExceptionalIndex.Group ⟨⟨⟨.F4 q, h⟩, by simp⟩, by simp⟩
  | ⟨.G2 q, h⟩ =>
      UnimodularExceptionalIndex.Group ⟨⟨⟨.G2 q, h⟩, by simp⟩, by simp⟩
  | ⟨.twistedE6 q, h⟩ =>
      TypeTwistedE6LieIndex.Group ⟨⟨.twistedE6 q, h⟩, by simp⟩
  | ⟨.trialityD4 q, h⟩ =>
      TypeTrialityD4LieIndex.Group ⟨⟨.trialityD4 q, h⟩, by simp⟩
  | ⟨.suzuki m, h⟩ => SuzukiLieIndex.Group ⟨⟨.suzuki m, h⟩, by simp⟩
  | ⟨.reeG2 m, h⟩ => ReeG2LieIndex.Group ⟨⟨.reeG2 m, h⟩, by simp⟩
  | ⟨.reeF4 m, h⟩ => ReeF4LieIndex.Group ⟨⟨.reeF4 m, h⟩, by simp⟩
  | ⟨.tits, h⟩ => ReeF4LieIndex.Group ⟨⟨.tits, h⟩, by simp⟩

noncomputable instance (d : ValidLieTypeIndex) : Group d.Group := by
  obtain ⟨d, h⟩ := d
  cases d <;> infer_instance

/-- The concrete group represented by an index on the classification list. -/
abbrev CFSGIndex.Group : CFSGIndex → Type
  | .cyclic p _ => Multiplicative (ZMod p)
  | .alternating degree _ => alternatingGroup (Fin degree)
  | .lie index => index.Group
  | .sporadic name => name.Group

noncomputable instance (i : CFSGIndex) : Group i.Group := by
  cases i <;> infer_instance

universe u

/-- **Classification of finite simple groups, statement only.** Every finite simple group is
isomorphic to one of the explicitly constructed groups on the classification list. -/
def ClassificationStatement : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] [IsSimpleGroup G],
    ∃ i : CFSGIndex, Nonempty (G ≃* i.Group)

/-- The universe-zero classification statement implies the statement in every universe. -/
theorem classificationStatement_of_zero (h : ClassificationStatement.{0}) :
    ClassificationStatement.{u} :=
  exists_mulEquiv_of_forall_finite_isSimpleGroup_zero CFSGIndex.Group h

end TauCeti
