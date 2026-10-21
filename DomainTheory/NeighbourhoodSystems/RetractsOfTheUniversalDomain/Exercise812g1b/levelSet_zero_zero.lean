/-ai
The level set of height 0 and mask 0 is empty.

No bit of the zero mask is set.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812g1b.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- `levelSet 0 0 = ∅`: at level `0`, mask `0` has no set bits. -/
theorem levelSet_zero_zero : levelSet 0 0 = ∅ := by
  ext n; simp [levelSet, Nat.zero_testBit]

end DomainTheory.NeighbourhoodSystems
