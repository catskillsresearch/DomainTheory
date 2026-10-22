module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.MemA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.prodN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.mem_prodN

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Example62A

open NeighborhoodSystem ApproximableMap ExampleB

variable {β : Type*} {n : ℕ}

theorem prodN_subset {X X' : Fin n → Set β} : prodN X ⊆ prodN X' ↔ ∀ j, X j ⊆ X' j := by
  constructor
  · intro h j b hb; exact h (show (j, b) ∈ prodN X from hb)
  · intro h p hp; exact h p.1 hp

end Example62A

end DomainTheory.NeighbourhoodSystems
