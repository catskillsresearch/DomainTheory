/-ai
The strict comparison code of two rational codes equals one if and only if the first decoded rational is strictly less than the second.

Unfolding the strict comparison and cancelling the pairing, the swapped comparison code is at most one, so one minus that code equals one exactly when the swapped comparison equals zero, and that happens exactly when the swapped comparison differs from one. The comparison code equals one exactly on the weak order, so failure of the swapped weak order is the strict order.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.ratLeCode_eq_one_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.ratLeCode_le_one

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive


theorem ratLtCode_eq_one_iff (c1 c2 : ℕ) :
    ratLtCode (Nat.pair c1 c2) = 1 ↔ decodeRat c1 < decodeRat c2 := by
  unfold ratLtCode
  rw [unpair_pair_fst, unpair_pair_snd]
  have h1 := ratLeCode_le_one (Nat.pair c2 c1)
  rw [show (1 : ℕ) - ratLeCode (Nat.pair c2 c1) = 1 ↔ ratLeCode (Nat.pair c2 c1) = 0 from by omega,
    show ratLeCode (Nat.pair c2 c1) = 0 ↔ ¬ ratLeCode (Nat.pair c2 c1) = 1 from by omega,
    ratLeCode_eq_one_iff, not_le]

end DomainTheory.NeighbourhoodSystems
