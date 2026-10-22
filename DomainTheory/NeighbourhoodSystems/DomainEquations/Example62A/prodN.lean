module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.MemA

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Example62A

open NeighborhoodSystem ApproximableMap ExampleB

variable {β : Type*} {n : ℕ}

/-- The *proper product* neighbourhood `⋃_{j<n} {j} × X_j`: token `(j, b)` lies in it iff `b ∈ X_j`.
This is the `n`-ary analogue of `prodNbhd` (Definition 3.1). -/
def prodN (X : Fin n → Set β) : Set (Fin n × β) := {p | p.2 ∈ X p.1}

end Example62A

end DomainTheory.NeighbourhoodSystems
