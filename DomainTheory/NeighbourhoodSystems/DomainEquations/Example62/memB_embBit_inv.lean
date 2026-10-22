module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.embBit
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.mem_embBit
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.embBit_cone
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.embBit_injective

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

/-- If `bW ∈ B` then `W ∈ B`: a `b`-prefixed neighbourhood that lands in `B` must be `b·(cone w')`,
so `W = cone w'`. -/
theorem memB_embBit_inv {b : Bool} {W : Set Str} (h : B.mem (embBit b W)) : B.mem W := by
  obtain ⟨σ, hσ⟩ := h
  have hmem : σ ∈ embBit b W := hσ ▸ (show σ ∈ cone σ from List.prefix_rfl)
  obtain ⟨w', rfl, -⟩ := hmem
  rw [← embBit_cone] at hσ
  rw [embBit_injective hσ]
  exact memB_cone w'

end Example62

end DomainTheory.NeighbourhoodSystems
