/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.SpecialIsogeny
public import TauCeti.GroupTheory.SpecificGroups.CFSG.ReeG2.Carrier
public import TauCeti.GroupTheory.SpecificGroups.CFSG.HalfFrobenius
public import TauCeti.GroupTheory.FixedPointCandidate

/-!
# The Ree G2 Steinberg map and candidate group

The signed-minor construction gives the exceptional endomorphism of the characteristic-three
short-root carrier. Its odd power is the Steinberg map for a validated Ree G2 index. The candidate
is the derived subgroup of its fixed points modulo the centre of that derived subgroup.

These are the L2 and L3 constructions of `TauCetiRoadmap/CFSGStatement/README.md`. The ambient
carrier is explicit and has not been identified with the pinned simply connected G2 group scheme;
transfer to that group requires such an identification. No finiteness or simplicity is assumed
or proved here. The conventions follow Carter, *Simple Groups of Lie Type*, §§12.3 and 13.
-/

public section

namespace TauCeti.ReeG2LieIndex

noncomputable section

variable (d : ReeG2LieIndex)

/-- The exceptional endomorphism of the Ree G2 ambient carrier. -/
def halfFrobenius : d.AmbientGroup →* d.AmbientGroup :=
  G2ShortRoot.PrimeField.specialIsogeny d.1.Closure

/-- The half-Frobenius squares to the prime-field Frobenius. -/
@[simp] theorem halfFrobenius_halfFrobenius (g : d.AmbientGroup) :
    d.halfFrobenius (d.halfFrobenius g) = d.primeFrobenius g := by
  rw [halfFrobenius, primeFrobenius_def,
    G2ShortRoot.PrimeField.specialIsogeny_specialIsogeny]

private theorem carrierNode_lengthPerm (i : Fin d.1.rank) :
    finCongr d.rank_eq_two (d.toSuzukiReeIndex.lengthPerm i) =
      Equiv.swap 0 1 (finCongr d.rank_eq_two i) := by
  obtain ⟨m, hvalid, rfl⟩ := d.exists_eq_of
  have hswap : lengthPermRankTwo = Equiv.swap 0 1 := by
    ext j
    rw [lengthPermRankTwo_apply]
    fin_cases j <;> decide
  simp [toSuzukiReeIndex, SuzukiReeIndex.lengthPerm_reeG2, Equiv.permCongr_def, hswap]

private theorem carrierExponent (i : Fin d.1.rank) :
    G2ShortRoot.PrimeField.specialIsogenyExponent (.inl (finCongr d.rank_eq_two i)) =
      d.toSuzukiReeIndex.exponent i := by
  obtain ⟨m, hvalid, rfl⟩ := d.exists_eq_of
  fin_cases i
  · have h := SuzukiReeIndex.exponent_of_not_isLongSimpleRoot
      (of m hvalid).toSuzukiReeIndex ⟨0, by change 0 < 2; decide⟩ (by
        change ¬ DynkinType.G2.IsLongSimpleRoot (0 : Fin 2)
        simp)
    rw [(of m hvalid).characteristic_eq_three] at h
    simpa using h.symm
  · have h := SuzukiReeIndex.exponent_of_isLongSimpleRoot
      (of m hvalid).toSuzukiReeIndex ⟨1, by change 1 < 2; decide⟩ (by
        change DynkinType.G2.IsLongSimpleRoot (1 : Fin 2)
        simp)
    simpa [Fin.ext_iff] using h.symm

/-- The half-Frobenius has the index's own root permutation and long/short exponents. -/
@[simp] theorem halfFrobenius_simpleRootSubgroup (i : Fin d.1.rank)
    (u : Multiplicative d.1.Closure) :
    d.halfFrobenius (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup (d.toSuzukiReeIndex.lengthPerm i)
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.toSuzukiReeIndex.exponent i)) := by
  obtain ⟨t, rfl⟩ := Multiplicative.ofAdd.surjective u
  rw [halfFrobenius, simpleRootSubgroup_def,
    G2ShortRoot.PrimeField.specialIsogeny_rootSubgroupPoints, simpleRootSubgroup_def,
    G2ShortRoot.PrimeField.specialIsogenyRootIndex_inl,
    carrierNode_lengthPerm, ← carrierExponent]
  rfl

/-- The Steinberg endomorphism is the recorded odd power of the exceptional endomorphism. -/
def steinberg : d.AmbientGroup →* d.AmbientGroup :=
  (show Monoid.End _ from d.halfFrobenius) ^ d.1.fieldExponent

private theorem halfFrobenius_iterate_two_mul (k : ℕ) (g : d.AmbientGroup) :
    (⇑d.halfFrobenius)^[2 * k] g = G2ShortRoot.PrimeField.frobenius k d.1.Closure g := by
  induction k generalizing g with
  | zero => simp [G2ShortRoot.PrimeField.frobenius_zero]
  | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega,
        Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
        halfFrobenius_halfFrobenius, primeFrobenius_def,
        Nat.add_comm k 1, G2ShortRoot.PrimeField.frobenius_add, MonoidHom.comp_apply]

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
    G2ShortRoot.PrimeField.frobenius_rootSubgroupPoints]
  congr 2
  simp only [toAdd_ofAdd, ← pow_mul, characteristic_eq_three, Nat.mul_comm]

/-- The fixed subgroup of the Ree G2 Steinberg endomorphism. -/
abbrev FixedPoints : Type := ↥(fixedSubgroup d.steinberg)

/-- The Ree G2 candidate: the derived subgroup of the Steinberg fixed points modulo its own
centre. This definition carries no assertion of finiteness, perfectness, or simplicity. -/
abbrev Group : Type := FixedPointCandidate d.steinberg

example : _root_.Group d.Group := inferInstance

end

end TauCeti.ReeG2LieIndex
