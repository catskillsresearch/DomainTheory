/-ai
A natural number k lies in the neighbourhood indexed by n if and only if the k-th bit of n is unset.

This is the defining membership condition, so the equivalence is definitional.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78.nbhd

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example78

open Domain.Recursive NeighborhoodSystem

@[simp] theorem mem_nbhd {n k : ℕ} : k ∈ nbhd n ↔ n.testBit k = false := Iff.rfl

end DomainTheory.NeighbourhoodSystems.Example78
