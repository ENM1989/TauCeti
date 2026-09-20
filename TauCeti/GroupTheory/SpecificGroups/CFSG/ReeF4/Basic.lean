/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.QuotientSpecialIsogeny
public import TauCeti.GroupTheory.SpecificGroups.CFSG.ReeF4.Carrier
public import TauCeti.GroupTheory.SpecificGroups.CFSG.HalfFrobenius
public import TauCeti.GroupTheory.FixedPointCandidate

/-!
# The Ree F4 Steinberg map and candidate group

The represented quotient constructs the exceptional endomorphism of the characteristic-two
short-root carrier. Its odd power is the Steinberg map for a validated Ree F4 index. The candidate
is the derived subgroup of its fixed points modulo the centre of that derived subgroup.

The ambient carrier is explicit and has not been identified with the pinned simply connected
F4 group scheme;
transfer to that group requires such an identification. No finiteness or simplicity is assumed
or proved here. The conventions follow Carter, *Simple Groups of Lie Type*, §14.
-/

public section

namespace TauCeti.ReeF4LieIndex

noncomputable section

variable (d : ReeF4LieIndex)

/-- The exceptional endomorphism of the Ree F4 ambient carrier. -/
def halfFrobenius : d.AmbientGroup →* d.AmbientGroup :=
  F4ShortRoot.PrimeField.specialIsogeny d.1.Closure

/-- The half-Frobenius squares to the prime-field Frobenius. -/
@[simp] theorem halfFrobenius_halfFrobenius (g : d.AmbientGroup) :
    d.halfFrobenius (d.halfFrobenius g) = d.primeFrobenius g := by
  rw [halfFrobenius, primeFrobenius_def,
    F4ShortRoot.PrimeField.specialIsogeny_specialIsogeny]

private theorem carrierNode_lengthPerm (i : Fin d.1.rank) :
    finCongr d.rank_eq_four (d.toSuzukiReeIndex.lengthPerm i) =
      Fin.revPerm (finCongr d.rank_eq_four i) := by
  obtain ⟨m, hvalid, rfl⟩ := d.exists_eq_of
  simp [toSuzukiReeIndex, SuzukiReeIndex.lengthPerm_reeF4, Equiv.permCongr_def,
    lengthPermF4_apply]

private theorem carrierExponent (i : Fin d.1.rank) :
    F4ShortRoot.isogenyExponent (.inl (finCongr d.rank_eq_four i)) =
      d.toSuzukiReeIndex.exponent i := by
  rw [exponent_eq]
  have h : ∀ j : Fin 4, F4ShortRoot.isogenyExponent (.inl j) =
      if (j : ℕ) < 2 then 1 else 2 := by decide
  exact h (finCongr d.rank_eq_four i)

/-- The half-Frobenius has the index's own root permutation and long/short exponents. -/
@[simp] theorem halfFrobenius_simpleRootSubgroup (i : Fin d.1.rank)
    (u : Multiplicative d.1.Closure) :
    d.halfFrobenius (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup (d.toSuzukiReeIndex.lengthPerm i)
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.toSuzukiReeIndex.exponent i)) := by
  rw [halfFrobenius, simpleRootSubgroup_def,
    F4ShortRoot.PrimeField.specialIsogeny_rootSubgroupPoints, simpleRootSubgroup_def,
    carrierNode_lengthPerm, ← carrierExponent]
  rfl

/-- The Steinberg endomorphism is the recorded odd power of the exceptional endomorphism. -/
def steinberg : d.AmbientGroup →* d.AmbientGroup :=
  (show Monoid.End _ from d.halfFrobenius) ^ d.1.fieldExponent

private theorem halfFrobenius_iterate_two_mul (k : ℕ) (g : d.AmbientGroup) :
    (⇑d.halfFrobenius)^[2 * k] g = F4ShortRoot.PrimeField.frobenius k d.1.Closure g := by
  induction k generalizing g with
  | zero => simp [F4ShortRoot.PrimeField.frobenius_zero]
  | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega,
        Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
        halfFrobenius_halfFrobenius, primeFrobenius_def,
        Nat.add_comm k 1, F4ShortRoot.PrimeField.frobenius_add, MonoidHom.comp_apply]

/-- The square of the Steinberg endomorphism is the field-order Frobenius. -/
@[simp] theorem steinberg_steinberg (g : d.AmbientGroup) :
    d.steinberg (d.steinberg g) = d.frobenius g := by
  have hpow : ⇑d.steinberg = (⇑d.halfFrobenius)^[d.1.fieldExponent] :=
    Monoid.End.coe_pow (M := d.AmbientGroup) d.halfFrobenius d.1.fieldExponent
  rw [hpow, ← Function.iterate_add_apply, ← two_mul,
    halfFrobenius_iterate_two_mul, frobenius_def]

/-- The odd iterate exchanges the numbered roots with the prescribed parameter power. -/
@[simp] theorem steinberg_simpleRootSubgroup (i : Fin d.1.rank)
    (u : Multiplicative d.1.Closure) :
    d.steinberg (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup (d.toSuzukiReeIndex.lengthPerm i)
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^
          (d.1.characteristic ^ d.toSuzukiReeIndex.halfExponent *
            d.toSuzukiReeIndex.exponent i))) := by
  have hpow : ⇑d.steinberg = (⇑d.halfFrobenius)^[d.1.fieldExponent] :=
    Monoid.End.coe_pow (M := d.AmbientGroup) d.halfFrobenius d.1.fieldExponent
  rw [hpow, d.toSuzukiReeIndex.fieldExponent_eq_two_mul_halfExponent_add_one,
    Function.iterate_succ_apply, halfFrobenius_simpleRootSubgroup,
    halfFrobenius_iterate_two_mul, simpleRootSubgroup_def,
    F4ShortRoot.PrimeField.frobenius_rootSubgroupPoints]
  congr 2
  simp only [toAdd_ofAdd, ← pow_mul, characteristic_eq_two, Nat.mul_comm]

/-- The fixed subgroup of the Ree F4 Steinberg endomorphism. -/
abbrev FixedPoints : Type := ↥(fixedSubgroup d.steinberg)

/-- The Ree F4 candidate: the derived subgroup of the Steinberg fixed points modulo its own
centre. This definition carries no assertion of finiteness, perfectness, or simplicity. -/
abbrev Group : Type := FixedPointCandidate d.steinberg

example : _root_.Group d.Group := inferInstance

end

end TauCeti.ReeF4LieIndex
