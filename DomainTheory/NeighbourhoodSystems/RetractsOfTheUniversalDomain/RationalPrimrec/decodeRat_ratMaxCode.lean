/-ai
The maximum code of two rational codes decodes to the maximum of the two decoded rationals.

Unfolding the maximum code and cancelling the pairing, the comparison of the two decoded rationals splits the argument. If the first is at most the second, the comparison code equals one, selection returns the second code, and the maximum is the second rational. Otherwise the comparison code differs from one, and since it is at most one it equals zero, so selection returns the first code and the maximum is the first rational.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.ratLeCode_eq_one_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.ratLeCode_le_one

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive



















theorem decodeRat_ratMaxCode (c1 c2 : ℕ) :
    decodeRat (ratMaxCode (Nat.pair c1 c2)) = max (decodeRat c1) (decodeRat c2) := by
  unfold ratMaxCode
  rw [unpair_pair_fst, unpair_pair_snd]
  by_cases h : decodeRat c1 ≤ decodeRat c2
  · rw [(ratLeCode_eq_one_iff c1 c2).mpr h, selectFn_one, max_eq_right h]
  · have hf : ratLeCode (Nat.pair c1 c2) ≠ 1 := fun he => h ((ratLeCode_eq_one_iff c1 c2).mp he)
    have hf0 : ratLeCode (Nat.pair c1 c2) = 0 := by
      have := ratLeCode_le_one (Nat.pair c1 c2); omega
    rw [hf0, selectFn_zero, max_eq_left ((not_le.mp h).le)]

end DomainTheory.NeighbourhoodSystems
