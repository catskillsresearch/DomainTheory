/-ai
The minimum code of two rational codes decodes to the minimum of the two decoded rationals.

Unfolding the minimum code and cancelling the pairing, the comparison of the two decoded rationals splits the argument. If the first is at most the second, the comparison code equals one, selection returns the first code, and the minimum is the first rational. Otherwise the comparison code differs from one, and since it is at most one it equals zero, so selection returns the second code and the minimum is the second rational.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.ratLeCode_eq_one_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.ratLeCode_le_one

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive


theorem decodeRat_ratMinCode (c1 c2 : ℕ) :
    decodeRat (ratMinCode (Nat.pair c1 c2)) = min (decodeRat c1) (decodeRat c2) := by
  unfold ratMinCode
  rw [unpair_pair_fst, unpair_pair_snd]
  by_cases h : decodeRat c1 ≤ decodeRat c2
  · rw [(ratLeCode_eq_one_iff c1 c2).mpr h, selectFn_one, min_eq_left h]
  · have hf : ratLeCode (Nat.pair c1 c2) ≠ 1 := fun he => h ((ratLeCode_eq_one_iff c1 c2).mp he)
    have hf0 : ratLeCode (Nat.pair c1 c2) = 0 := by
      have := ratLeCode_le_one (Nat.pair c1 c2); omega
    rw [hf0, selectFn_zero, min_eq_right ((not_le.mp h).le)]

end DomainTheory.NeighbourhoodSystems
