module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- The intersection of the sets in `M`, taken inside the base set `base` (so the empty list gives
`base`, matching the convention 1.1a where the empty intersection is `Δ`). -/
def interList (base : Set β) : List (Set β) → Set β
  | [] => base
  | Y :: M => Y ∩ interList base M

end DomainTheory.NeighbourhoodSystems
