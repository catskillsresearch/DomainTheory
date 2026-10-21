/-ai
The bit test is at most one.

Unfolding the test, the remainder modulo two of the iterated quotient is zero or one,
and arithmetic gives the bound in both cases.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem


theorem myTestBit_le_one (m ℓ : ℕ) : myTestBit m ℓ ≤ 1 := by
  unfold myTestBit
  rcases Nat.mod_two_eq_zero_or_one (myDivPow2 m ℓ) with h | h <;> omega

end DomainTheory.NeighbourhoodSystems
