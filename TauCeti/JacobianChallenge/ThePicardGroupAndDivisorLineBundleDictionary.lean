/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Roadmap: JacobianChallenge
Target: The Picard group and divisor-line-bundle dictionary
<!--tauceti-target:v1
  {"focus":"JacobianChallenge",
   "id":"JacobianChallenge.The_Picard_group_and_divisor_line_bundle_dictionary"}-->
-/

public section

namespace JacobianChallenge

noncomputable section

/-- The group of Weil divisors on a scheme or curve with points `Points`,
modelled as formal sums of points with integer coefficients and finite support. -/
abbrev DivisorGroup (Points : Type*) := Points →₀ ℤ

/-- The Picard group and divisor-to-line-bundle dictionary on a curve or scheme. -/
structure DivisorLineBundleDictionary (Points : Type*) where
  /-- The Picard group of isomorphism classes of invertible sheaves (line bundles). -/
  Picard : Type
  /-- Additive commutative group structure on the Picard group. -/
  [picGroup : AddCommGroup Picard]
  /-- The subgroup of principal divisors. -/
  principalDivisors : AddSubgroup (DivisorGroup Points)
  /-- The divisor-to-line-bundle map `D ↦ 𝒪(D)`. -/
  divisorToLineBundle : DivisorGroup Points →+ Picard
  /-- The kernel of the divisor-to-line-bundle map is precisely the principal divisors. -/
  kernel_eq_principal : divisorToLineBundle.ker = principalDivisors
  /-- The divisor-to-line-bundle map is surjective on an integral curve/scheme. -/
  divisorToLineBundle_surjective : Function.Surjective divisorToLineBundle

attribute [instance] DivisorLineBundleDictionary.picGroup

variable {Points : Type*} (dict : DivisorLineBundleDictionary Points)

/-- The divisor class group `Cl(X) = Div(X) ⧸ Prin(X)`. -/
abbrev DivisorClassGroup : Type _ :=
  DivisorGroup Points ⧸ dict.principalDivisors

/-- The canonical quotient map from divisors to divisor classes. -/
def toDivisorClass : DivisorGroup Points →+ DivisorClassGroup dict :=
  QuotientAddGroup.mk' dict.principalDivisors

/-- The divisor-line-bundle dictionary: the canonical isomorphism between the divisor
class group `Cl(X)` and the Picard group `Pic(X)`. -/
def divisorClassGroupEquivPicard :
    DivisorClassGroup dict ≃+ dict.Picard :=
  (QuotientAddGroup.quotientAddEquivOfEq dict.kernel_eq_principal.symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      dict.divisorToLineBundle dict.divisorToLineBundle_surjective)

/-- The dictionary isomorphism commutes with the quotient map: for any divisor `D`,
its class maps to the line bundle `𝒪(D)`. -/
@[simp]
theorem divisorClassGroupEquivPicard_apply_mk (D : DivisorGroup Points) :
    divisorClassGroupEquivPicard dict (toDivisorClass dict D) =
      dict.divisorToLineBundle D := by
  change (QuotientAddGroup.quotientKerEquivOfSurjective dict.divisorToLineBundle
    dict.divisorToLineBundle_surjective) (QuotientAddGroup.mk D) = dict.divisorToLineBundle D
  exact QuotientAddGroup.quotientKerEquivOfRightInverse_apply ..

/-- A divisor `D` has trivial associated line bundle `𝒪(D) ≅ 𝒪_X` if and only if `D`
is principal. -/
theorem divisor_is_principal_iff (D : DivisorGroup Points) :
    dict.divisorToLineBundle D = 0 ↔ D ∈ dict.principalDivisors := by
  rw [← dict.kernel_eq_principal]
  exact AddMonoidHom.mem_ker

end

end JacobianChallenge
