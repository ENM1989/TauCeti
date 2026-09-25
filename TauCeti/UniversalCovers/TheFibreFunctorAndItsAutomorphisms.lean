/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.Basic
public import Mathlib.Logic.Equiv.Defs

/-!
# Roadmap: UniversalCovers
Target: The fibre functor and its automorphisms.
<!--tauceti-target:v1
  {"focus":"UniversalCovers",
   "id":"UniversalCovers.The_fibre_functor_and_its_automorphisms"}-->
-/

public section

namespace UniversalCovers

open scoped Topology

universe u v

/-- A covering space over a base topological space with basepoint, universe polymorphic
in both the base space and the total space. -/
structure CoveringOver (B : Type*) [TopologicalSpace B] (b₀ : B) where
  /-- The total space of the covering. -/
  Total : Type*
  /-- The topology on the total space. -/
  top : TopologicalSpace Total
  /-- The covering projection map. -/
  proj : Total → B
  /-- Covering map property of the projection. -/
  isCovering : @IsCoveringMap Total B top _ proj

attribute [instance] CoveringOver.top

/-- Morphism between covering spaces over B. -/
structure CoveringHom {B : Type*} [TopologicalSpace B] {b₀ : B}
    (E₁ E₂ : CoveringOver B b₀) where
  /-- The underlying map between total spaces. -/
  toFun : E₁.Total → E₂.Total
  /-- Continuity of the morphism. -/
  continuous_toFun : Continuous toFun
  /-- Commutativity with the projection. -/
  comm : E₂.proj ∘ toFun = E₁.proj

/-- The identity morphism of a covering space. -/
def idHom {B : Type*} [TopologicalSpace B] {b₀ : B} (E : CoveringOver B b₀) :
    CoveringHom E E :=
  ⟨id, continuous_id, rfl⟩

/-- Composition of covering space morphisms. -/
def compHom {B : Type*} [TopologicalSpace B] {b₀ : B}
    {E₁ E₂ E₃ : CoveringOver B b₀}
    (g : CoveringHom E₂ E₃) (f : CoveringHom E₁ E₂) :
    CoveringHom E₁ E₃ :=
  ⟨g.toFun ∘ f.toFun, g.continuous_toFun.comp f.continuous_toFun, by
    have h : E₃.proj ∘ (g.toFun ∘ f.toFun) = (E₃.proj ∘ g.toFun) ∘ f.toFun := rfl
    rw [h, g.comm, f.comm]⟩

/-- The fibre functor taking a covering space to the preimage of the basepoint. -/
def fibreFunctor {B : Type*} [TopologicalSpace B] {b₀ : B}
    (E : CoveringOver B b₀) : Set E.Total :=
  { e : E.Total | E.proj e = b₀ }

/-- Action of a covering morphism on fibres. -/
def fibreMap {B : Type*} [TopologicalSpace B] {b₀ : B}
    {E₁ E₂ : CoveringOver B b₀} (f : CoveringHom E₁ E₂)
    (x : fibreFunctor E₁) : fibreFunctor E₂ :=
  ⟨f.toFun x.1, by
    change E₂.proj (f.toFun x.1) = b₀
    have h : E₂.proj (f.toFun x.1) = (E₂.proj ∘ f.toFun) x.1 := rfl
    rw [h, f.comm]
    exact x.2⟩

/-- The fibre functor preserves identity morphisms. -/
theorem fibreMap_id {B : Type*} [TopologicalSpace B] {b₀ : B}
    (E : CoveringOver B b₀) (x : fibreFunctor E) :
    fibreMap (idHom E) x = x := by
  ext
  rfl

/-- The fibre functor preserves composition of morphisms. -/
theorem fibreMap_comp {B : Type*} [TopologicalSpace B] {b₀ : B}
    {E₁ E₂ E₃ : CoveringOver B b₀}
    (g : CoveringHom E₂ E₃) (f : CoveringHom E₁ E₂)
    (x : fibreFunctor E₁) :
    fibreMap (compHom g f) x = fibreMap g (fibreMap f x) := by
  ext
  rfl

/-- Natural automorphisms of the fibre functor on covering spaces over `(B, b₀)`. -/
structure FibreAutomorphism (B : Type u) [TopologicalSpace B] (b₀ : B) where
  /-- Permutation assigned to the fibre of each covering space. -/
  app : (E : CoveringOver.{u, v} B b₀) → Equiv.Perm (fibreFunctor E)
  /-- Naturality condition: compatibility with all covering morphisms. -/
  naturality : ∀ {E₁ E₂ : CoveringOver.{u, v} B b₀} (f : CoveringHom E₁ E₂)
    (x : fibreFunctor E₁),
    (app E₂).toFun (fibreMap f x) = fibreMap f ((app E₁).toFun x)

/-- The identity automorphism of the fibre functor. -/
def idFibreAut (B : Type u) [TopologicalSpace B] (b₀ : B) :
    FibreAutomorphism.{u, v} B b₀ :=
  ⟨fun _ ↦ Equiv.refl _, fun _ _ ↦ rfl⟩

/-- Composition of fibre functor automorphisms. -/
def compFibreAut {B : Type u} [TopologicalSpace B] {b₀ : B}
    (α β : FibreAutomorphism.{u, v} B b₀) : FibreAutomorphism.{u, v} B b₀ where
  app E := (β.app E).trans (α.app E)
  naturality f x := by
    change (α.app _).toFun ((β.app _).toFun (fibreMap f x)) =
      fibreMap f ((α.app _).toFun ((β.app _).toFun x))
    rw [β.naturality f x, α.naturality f ((β.app _).toFun x)]

end UniversalCovers
