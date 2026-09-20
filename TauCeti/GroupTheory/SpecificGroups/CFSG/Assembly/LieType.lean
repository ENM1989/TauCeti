/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.GraphTwisted
public import TauCeti.GroupTheory.SpecificGroups.CFSG.ReeG2.Basic
public import TauCeti.GroupTheory.SpecificGroups.CFSG.ReeF4.Basic
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Suzuki.Basic
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Tits.Basic

/-!
# The concrete carrier and Steinberg map of every valid Lie-type index

The thirteen ordinary and graph-twisted families use their existing assembly. The four
half-Frobenius families use their explicit Suzuki, Ree, or Tits endomorphism. Every branch
retains the validity proof of the input index; no carrier is assigned to an invalid index.

The candidate group is uniformly the derived subgroup of the fixed points modulo its centre.
The explicit carriers have not been identified with the pinned simply connected groups; those
identifications remain milestone L5. No finiteness or simplicity of a candidate is asserted.

This completes the group-level assembly of milestones L2 and L3 needed by A0 of
`TauCetiRoadmap/CFSGStatement/README.md`. The construction follows the family modules it imports.
-/

public section

namespace TauCeti.ValidLieTypeIndex

noncomputable section

/-- The explicit algebraic-closure-valued carrier of the validated family. -/
@[expose] def AmbientGroup : ValidLieTypeIndex → Type
  | ⟨.suzuki _, hv⟩ => (SuzukiLieIndex.toRankTwoBLieIndex ⟨⟨_, hv⟩, by simp⟩).AmbientGroup
  | ⟨.reeG2 _, hv⟩ => ReeG2LieIndex.AmbientGroup ⟨⟨_, hv⟩, by simp⟩
  | ⟨.reeF4 _, hv⟩ => ReeF4LieIndex.AmbientGroup ⟨⟨_, hv⟩, by simp⟩
  | ⟨.tits, hv⟩ => TitsLieIndex.AmbientGroup ⟨⟨_, hv⟩, by simp⟩
  | ⟨.A _ _, hv⟩ | ⟨.twistedA _ _, hv⟩ | ⟨.B _ _, hv⟩
  | ⟨.C _ _, hv⟩ | ⟨.D _ _, hv⟩ | ⟨.twistedD _ _, hv⟩
  | ⟨.E6 _, hv⟩ | ⟨.E7 _, hv⟩ | ⟨.E8 _, hv⟩
  | ⟨.F4 _, hv⟩ | ⟨.G2 _, hv⟩ | ⟨.twistedE6 _, hv⟩
  | ⟨.trialityD4 _, hv⟩ =>
      GraphTwistedIndex.AmbientGroup ⟨⟨_, hv⟩, by simp⟩

/-- The assembled carrier has the group structure of its family. -/
instance instGroupAmbientGroup : (d : ValidLieTypeIndex) → Group d.AmbientGroup
  | ⟨.suzuki _, hv⟩ =>
      inferInstanceAs (Group
        ((SuzukiLieIndex.toRankTwoBLieIndex ⟨⟨_, hv⟩, by simp⟩).AmbientGroup))
  | ⟨.reeG2 _, hv⟩ => inferInstanceAs (Group (ReeG2LieIndex.AmbientGroup ⟨⟨_, hv⟩, by simp⟩))
  | ⟨.reeF4 _, hv⟩ => inferInstanceAs (Group (ReeF4LieIndex.AmbientGroup ⟨⟨_, hv⟩, by simp⟩))
  | ⟨.tits, hv⟩ => inferInstanceAs (Group (TitsLieIndex.AmbientGroup ⟨⟨_, hv⟩, by simp⟩))
  | ⟨.A _ _, hv⟩ | ⟨.twistedA _ _, hv⟩ | ⟨.B _ _, hv⟩
  | ⟨.C _ _, hv⟩ | ⟨.D _ _, hv⟩ | ⟨.twistedD _ _, hv⟩
  | ⟨.E6 _, hv⟩ | ⟨.E7 _, hv⟩ | ⟨.E8 _, hv⟩
  | ⟨.F4 _, hv⟩ | ⟨.G2 _, hv⟩ | ⟨.twistedE6 _, hv⟩
  | ⟨.trialityD4 _, hv⟩ =>
      inferInstanceAs (Group (GraphTwistedIndex.AmbientGroup ⟨⟨_, hv⟩, by simp⟩))

/-- The family's numbered positive simple root subgroups. -/
def simpleRootSubgroup :
    (d : ValidLieTypeIndex) → Fin d.rank → Multiplicative d.Closure →* d.AmbientGroup
  | ⟨.suzuki _, hv⟩ => (SuzukiLieIndex.toRankTwoBLieIndex ⟨⟨_, hv⟩, by simp⟩).simpleRootSubgroup
  | ⟨.reeG2 _, hv⟩ => ReeG2LieIndex.simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩
  | ⟨.reeF4 _, hv⟩ => ReeF4LieIndex.simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩
  | ⟨.tits, hv⟩ => TitsLieIndex.simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩
  | ⟨.A _ _, hv⟩ | ⟨.twistedA _ _, hv⟩ | ⟨.B _ _, hv⟩
  | ⟨.C _ _, hv⟩ | ⟨.D _ _, hv⟩ | ⟨.twistedD _ _, hv⟩
  | ⟨.E6 _, hv⟩ | ⟨.E7 _, hv⟩ | ⟨.E8 _, hv⟩
  | ⟨.F4 _, hv⟩ | ⟨.G2 _, hv⟩ | ⟨.twistedE6 _, hv⟩
  | ⟨.trialityD4 _, hv⟩ =>
      GraphTwistedIndex.simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩

/-- The actual Steinberg endomorphism on the carrier of each valid Lie-type index. -/
def steinberg : (d : ValidLieTypeIndex) → d.AmbientGroup →* d.AmbientGroup
  | ⟨.suzuki _, hv⟩ => SuzukiLieIndex.steinberg ⟨⟨_, hv⟩, by simp⟩
  | ⟨.reeG2 _, hv⟩ => ReeG2LieIndex.steinberg ⟨⟨_, hv⟩, by simp⟩
  | ⟨.reeF4 _, hv⟩ => ReeF4LieIndex.steinberg ⟨⟨_, hv⟩, by simp⟩
  | ⟨.tits, hv⟩ => TitsLieIndex.steinberg ⟨⟨_, hv⟩, by simp⟩
  | ⟨.A _ _, hv⟩ | ⟨.twistedA _ _, hv⟩ | ⟨.B _ _, hv⟩
  | ⟨.C _ _, hv⟩ | ⟨.D _ _, hv⟩ | ⟨.twistedD _ _, hv⟩
  | ⟨.E6 _, hv⟩ | ⟨.E7 _, hv⟩ | ⟨.E8 _, hv⟩
  | ⟨.F4 _, hv⟩ | ⟨.G2 _, hv⟩ | ⟨.twistedE6 _, hv⟩
  | ⟨.trialityD4 _, hv⟩ =>
      GraphTwistedIndex.steinberg ⟨⟨_, hv⟩, by simp⟩

/-- On ordinary and graph-twisted indices the assembled map has the recorded diagram action
and field-order exponent. -/
theorem steinberg_simpleRootSubgroup_of_not_usesHalfFrobenius
    (d : ValidLieTypeIndex) (h : ¬ d.1.UsesHalfFrobenius) (i : Fin d.rank)
    (u : Multiplicative d.Closure) :
    d.steinberg (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup ((GraphTwistedIndex.diagramPerm ⟨d, h⟩) i)
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.fieldOrder)) := by
  obtain ⟨d, hv⟩ := d
  cases d
  all_goals first
  | exact GraphTwistedIndex.steinberg_simpleRootSubgroup ⟨⟨_, hv⟩, h⟩ i u
  | exact absurd (by simp [LieTypeIndex.usesHalfFrobenius_iff]) h

/-- On the Suzuki, Ree and Tits indices the assembled map exchanges root lengths and raises
the parameter to the odd half-Frobenius exponent. -/
theorem steinberg_simpleRootSubgroup_of_usesHalfFrobenius
    (d : ValidLieTypeIndex) (h : d.1.UsesHalfFrobenius) (i : Fin d.rank)
    (u : Multiplicative d.Closure) :
    d.steinberg (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup ((SuzukiReeIndex.lengthPerm ⟨d, h⟩) i)
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^
          (d.characteristic ^ SuzukiReeIndex.halfExponent ⟨d, h⟩ *
            SuzukiReeIndex.exponent ⟨d, h⟩ i))) := by
  obtain ⟨d, hv⟩ := d
  cases d
  all_goals try { simp [LieTypeIndex.usesHalfFrobenius_iff] at h }
  · exact SuzukiLieIndex.steinberg_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u
  · exact ReeG2LieIndex.steinberg_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u
  · exact ReeF4LieIndex.steinberg_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u
  · rw [SuzukiReeIndex.halfExponent_tits, pow_zero, one_mul]
    exact TitsLieIndex.steinberg_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u

/-- The fixed subgroup of the family's Steinberg endomorphism. -/
abbrev FixedPoints (d : ValidLieTypeIndex) : Type := ↥(fixedSubgroup d.steinberg)

/-- The Lie-type candidate is the derived subgroup of the fixed points modulo its own centre.
No finiteness or simplicity instance is assumed or supplied. -/
abbrev Group (d : ValidLieTypeIndex) : Type := FixedPointCandidate d.steinberg

/-- On the thirteen ordinary or graph-twisted families, the assembled candidate is the
existing graph-twisted assembly's candidate. -/
theorem Group_eq_of_not_usesHalfFrobenius (d : ValidLieTypeIndex)
    (h : ¬ d.1.UsesHalfFrobenius) : d.Group = GraphTwistedIndex.Group ⟨d, h⟩ := by
  obtain ⟨d, hv⟩ := d
  cases d
  all_goals first
  | rfl
  | exact absurd (by simp [LieTypeIndex.usesHalfFrobenius_iff]) h

/-- The `suzuki` branch is the fixed-point candidate of its family. -/
theorem Group_suzuki (m : ℕ) (hv : (LieTypeIndex.suzuki m).Valid) :
    Group ⟨.suzuki m, hv⟩ = SuzukiLieIndex.Group ⟨⟨_, hv⟩, by simp⟩ := by
  rfl

/-- The `reeG2` branch is the fixed-point candidate of its family. -/
theorem Group_reeG2 (m : ℕ) (hv : (LieTypeIndex.reeG2 m).Valid) :
    Group ⟨.reeG2 m, hv⟩ = ReeG2LieIndex.Group ⟨⟨_, hv⟩, by simp⟩ := by
  rfl

/-- The `reeF4` branch is the fixed-point candidate of its family. -/
theorem Group_reeF4 (m : ℕ) (hv : (LieTypeIndex.reeF4 m).Valid) :
    Group ⟨.reeF4 m, hv⟩ = ReeF4LieIndex.Group ⟨⟨_, hv⟩, by simp⟩ := by
  rfl

/-- The separate Tits branch uses the first exceptional F4 iterate. -/
theorem Group_tits (hv : LieTypeIndex.tits.Valid) :
    Group ⟨.tits, hv⟩ = TitsLieIndex.Group ⟨⟨_, hv⟩, by simp⟩ := by
  rfl

example (d : ValidLieTypeIndex) : _root_.Group d.Group := inferInstance

end

end TauCeti.ValidLieTypeIndex
