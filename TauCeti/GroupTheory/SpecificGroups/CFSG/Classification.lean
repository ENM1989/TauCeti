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
  match d.1 with
  | .A .. | .twistedA .. => TypeALieIndex.Group ⟨d, by trivial⟩
  | .B .. => TypeBLieIndex.Group ⟨d, by trivial⟩
  | .C .. => TypeCLieIndex.Group ⟨d, by trivial⟩
  | .D .. => TypeDLieIndex.Group ⟨d, by trivial⟩
  | .twistedD .. => TypeTwistedDLieIndex.Group ⟨d, by trivial⟩
  | .E6 .. => TypeE6LieIndex.Group ⟨d, by trivial⟩
  | .E7 .. => TypeE7LieIndex.Group ⟨d, by trivial⟩
  | .E8 .. | .F4 .. | .G2 .. =>
      UnimodularExceptionalIndex.Group ⟨⟨d, by trivial⟩, by trivial⟩
  | .twistedE6 .. => TypeTwistedE6LieIndex.Group ⟨d, by trivial⟩
  | .trialityD4 .. => TypeTrialityD4LieIndex.Group ⟨d, by trivial⟩
  | .suzuki .. => SuzukiLieIndex.Group ⟨d, by trivial⟩
  | .reeG2 .. => ReeG2LieIndex.Group ⟨d, by trivial⟩
  | .reeF4 .. | .tits => ReeF4LieIndex.Group ⟨d, by trivial⟩

/-- The concrete group represented by an index on the classification list. -/
abbrev CFSGIndex.Group : CFSGIndex → Type
  | .cyclic p _ => Multiplicative (ZMod p)
  | .alternating degree _ => alternatingGroup (Fin degree)
  | .lie index => index.Group
  | .sporadic name => name.Group

instance (i : CFSGIndex) : Group i.Group := by
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
