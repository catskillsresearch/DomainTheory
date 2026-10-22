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
