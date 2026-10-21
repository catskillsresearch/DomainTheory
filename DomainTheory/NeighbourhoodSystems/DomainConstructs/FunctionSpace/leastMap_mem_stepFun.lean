/-ai
The least map of a list belongs to the step neighborhood of that list.

For each pair in the list, the intersection of relevant outputs at the pair's input is contained in the pair's output, which is the least-map relation for that pair.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.Basic
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.interYs_subset_of_mem

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}








































/-- **Proposition 3.9 (Scott 1981, PRG-19).** The least map `f₀` belongs to the neighbourhood:
`Xᵢ f₀ Yᵢ` for every `(Xᵢ, Yᵢ) ∈ L`. -/
theorem leastMap_mem_stepFun {L : List (Set α × Set β)} (hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2)
    (hcons : ∀ {X}, V₀.mem X → V₁.mem (interYs V₁.master L X)) : leastMap L hL hcons ∈ stepFun L := by
  intro p hp
  exact ⟨(hL p hp).1, (hL p hp).2, interYs_subset_of_mem hp⟩

end DomainTheory.NeighbourhoodSystems
