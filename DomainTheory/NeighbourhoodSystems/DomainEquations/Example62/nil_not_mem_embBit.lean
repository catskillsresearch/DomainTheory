module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.embBit
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.mem_embBit

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

theorem nil_not_mem_embBit {b : Bool} {X : Set Str} : ([] : Str) ∉ embBit b X := by
  rintro ⟨w', heq, -⟩; exact absurd heq (by simp)

end Example62

end DomainTheory.NeighbourhoodSystems
