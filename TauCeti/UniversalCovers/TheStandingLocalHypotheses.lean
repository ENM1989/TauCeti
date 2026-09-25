/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.Connected.LocallyPathConnected
public import Mathlib.Topology.Homotopy.Path

/-!
# Roadmap: UniversalCovers
Target: The standing local hypotheses.
<!--tauceti-target:v1
  {"focus":"UniversalCovers",
   "id":"UniversalCovers.The_standing_local_hypotheses"}-->
-/

public section

namespace UniversalCovers

open scoped Topology

/-- A topological space is semilocally simply connected if every point has an open neighborhood
such that every loop based at that point is null-homotopic in the ambient space. -/
def IsSemilocallySimplyConnected (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ x : X, ∃ U : Set X, IsOpen U ∧ ∃ hx : x ∈ U,
    ∀ (γ : Path (⟨x, hx⟩ : U) (⟨x, hx⟩ : U)),
      Path.Homotopic (γ.map continuous_subtype_val) (Path.refl x)

/-- Standing local topological hypotheses on a base space for universal covers:
path-connectedness, local path-connectedness, and semilocal simple connectedness. -/
structure LocalCoveringData (X : Type*) [TopologicalSpace X] : Prop where
  /-- The base space is path-connected. -/
  pathConnected : PathConnectedSpace X
  /-- The base space is locally path-connected. -/
  locallyPathConnected : LocallyPathConnectedSpace X
  /-- The base space is semilocally simply connected. -/
  semilocallySimplyConnected : IsSemilocallySimplyConnected X

/-- Any discrete space is semilocally simply connected, since singleton neighborhoods are
open and have only constant loops. -/
theorem isSemilocallySimplyConnected_of_discreteTopology
    (X : Type*) [TopologicalSpace X] [DiscreteTopology X] :
    IsSemilocallySimplyConnected X := by
  intro x
  refine ⟨{x}, isOpen_discrete {x}, ⟨Set.mem_singleton x, fun γ => ?_⟩⟩
  have hγ : γ.map continuous_subtype_val = Path.refl x := by
    ext t
    have h : (γ t).1 = x := (γ t).2
    exact h
  exact hγ ▸ Path.Homotopic.refl (Path.refl x)

/-- The singleton space `PUnit` is semilocally simply connected. -/
theorem isSemilocallySimplyConnected_punit : IsSemilocallySimplyConnected PUnit := by
  intro x
  refine ⟨Set.univ, isOpen_univ, ⟨trivial, fun γ => ?_⟩⟩
  convert Path.Homotopic.refl (Path.refl x)
  ext t

/-- Path-connectedness instance for `PUnit`. -/
instance punitPathConnectedSpace : PathConnectedSpace PUnit :=
  PathConnectedSpace.mk ⟨PUnit.unit⟩ (fun x _ => ⟨Path.refl x⟩)

/-- Canonical witness that the standing local hypotheses are satisfied on `PUnit`. -/
theorem localCoveringDataPUnit : LocalCoveringData PUnit where
  pathConnected := punitPathConnectedSpace
  locallyPathConnected := inferInstance
  semilocallySimplyConnected := isSemilocallySimplyConnected_punit

/-- For any space satisfying the standing local hypotheses, every point has
an open neighborhood in which every loop is contractible in the ambient space. -/
theorem standing_local_hypotheses_loop_nullhomotopic
    {X : Type*} [TopologicalSpace X] (d : LocalCoveringData X) (p : X) :
    ∃ U : Set X, IsOpen U ∧ ∃ hp : p ∈ U,
      ∀ (γ : Path (⟨p, hp⟩ : U) (⟨p, hp⟩ : U)),
        Path.Homotopic (γ.map continuous_subtype_val) (Path.refl p) := by
  exact d.semilocallySimplyConnected p

end UniversalCovers
