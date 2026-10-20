module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78.nbhd

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Example78

open Domain.Recursive NeighborhoodSystem

@[simp] theorem mem_nbhd {n k : ℕ} : k ∈ nbhd n ↔ n.testBit k = false := Iff.rfl

end DomainTheory.NeighbourhoodSystems.Example78
