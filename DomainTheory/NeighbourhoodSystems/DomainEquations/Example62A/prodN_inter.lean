/-ai
The intersection of two proper products is the proper product of the componentwise intersections.

Extensionality reduces both sides to the product membership condition, which matches.
ai-/
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

theorem prodN_inter {X X' : Fin n → Set β} :
    prodN X ∩ prodN X' = prodN (fun j => X j ∩ X' j) := by
  ext p; simp only [Set.mem_inter_iff, mem_prodN]

end Example62A

end DomainTheory.NeighbourhoodSystems
