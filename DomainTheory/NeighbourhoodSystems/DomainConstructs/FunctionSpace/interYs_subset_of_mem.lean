module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


/-- `interYs` contains `Yⱼ` whenever `Xⱼ ⊆ X`-indexed: in particular `interYs m L Xⱼ ⊆ Yⱼ` for
`(Xⱼ, Yⱼ) ∈ L`. -/
theorem interYs_subset_of_mem {m : Set β} {L : List (Set α × Set β)} {p : Set α × Set β}
    (hp : p ∈ L) : interYs m L p.1 ⊆ p.2 :=
  fun _ hz => (mem_interYs.mp hz).2 p hp subset_rfl

end DomainTheory.NeighbourhoodSystems
