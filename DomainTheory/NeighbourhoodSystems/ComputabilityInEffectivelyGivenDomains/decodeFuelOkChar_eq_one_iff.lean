/-ai
The fuel-bounded decode characteristic of a code equals 1 if and only if the fuel-bounded decode of that code is defined.

Induction on the fuel. With zero fuel both sides fail. With successor fuel, rewrite the characteristic by its body equation and match the tag, the first component of the unpairing. Tag 0 reduces the decode to sigma or nothing according as the payload is zero, and the one-bit selector matches that alternative. Tag 1 rewrites the decode as the singleton of a boolean-list decode, which is defined exactly when that list decode is defined. Tags 2 and 3 rewrite the decode as a concatenation or an intersection, whose characteristic is the product of the two recursive characteristics, and case analysis on the two recursive decodes matches the inductive hypotheses. A tag of the form t + 4 makes the decode fail.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeListBool_isSome_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeFuel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeFuel_succ_single
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeFuel_succ_cat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeFuel_succ_cap
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeFuel_succ_junk
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeFuel_pair_cat_isSome_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeFuel_pair_cap_isSome_iff

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

/-- **7.22i(b)1(e):** shallow link between fuel-bounded char decode and `decodeFuel`. -/
theorem decodeFuelOkChar_eq_one_iff (fuel c : ℕ) :
    decodeFuelOkChar fuel c = 1 ↔ (decodeFuel fuel c).isSome = true := by
  induction fuel generalizing c with
  | zero =>
    simp [decodeFuelOkChar, decodeFuel]
  | succ fuel ih =>
    simp only [decodeFuelOkChar]
    rw [decodeFuelOkCharBody_eq]
    match tag : c.unpair.1 with
    | 0 =>
      rw [show decodeFuel (fuel + 1) c = if c.unpair.2 = 0 then some .sigma else none from by
        by_cases hσ : c.unpair.2 = 0 <;> simp [decodeFuel, tag, hσ]]
      simp [selectFn_isOne_one_sub_sigma]
    | 1 =>
      rw [decodeFuel_succ_single fuel c tag]
      simp [decodeListBool_isSome_iff, Option.isSome_map]
    | 2 =>
      simp
      rw [decodeFuel_succ_cat fuel c tag, mulBit_eq_one_iff]
      have ih1 := ih c.unpair.2.unpair.1
      have ih2 := ih c.unpair.2.unpair.2
      cases hL : decodeFuel fuel c.unpair.2.unpair.1 <;>
        cases hR : decodeFuel fuel c.unpair.2.unpair.2 <;>
        simp [hL, hR, ih1, ih2]
    | 3 =>
      simp
      rw [decodeFuel_succ_cap fuel c tag, mulBit_eq_one_iff]
      have ih1 := ih c.unpair.2.unpair.1
      have ih2 := ih c.unpair.2.unpair.2
      cases hL : decodeFuel fuel c.unpair.2.unpair.1 <;>
        cases hR : decodeFuel fuel c.unpair.2.unpair.2 <;>
        simp [hL, hR, ih1, ih2]
    | t + 4 =>
      rw [decodeFuel_succ_junk fuel c (by omega)]
      simp

end Exercise722

end DomainTheory.NeighbourhoodSystems
