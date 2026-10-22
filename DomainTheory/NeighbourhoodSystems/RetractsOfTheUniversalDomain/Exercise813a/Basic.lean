module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812g4

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a.GeneratedBy
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a.bitmaskOf
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a.generator
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a.testBit_sum_two_pow
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a.testBit_bitmaskOf

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem


@[simp] theorem mem_generator {i n : ℕ} : n ∈ generator i ↔ n.testBit i = true := Iff.rfl

end DomainTheory.NeighbourhoodSystems
