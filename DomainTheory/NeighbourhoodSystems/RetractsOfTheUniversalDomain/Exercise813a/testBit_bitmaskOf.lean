/-ai
The i-th bit of the bitmask of a finite set is set exactly when i belongs to the set.

This is the bit test for a sum of distinct powers of two.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812g4
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a.GeneratedBy
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a.testBit_sum_two_pow
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a.bitmaskOf

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

@[simp] theorem testBit_bitmaskOf {s : Finset ℕ} {i : ℕ} : (bitmaskOf s).testBit i ↔ i ∈ s :=
  testBit_sum_two_pow

end DomainTheory.NeighbourhoodSystems
