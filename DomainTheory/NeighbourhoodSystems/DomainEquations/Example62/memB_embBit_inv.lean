/-ai
If the tagging of a set of binary strings by a boolean is a neighbourhood of the binary-sequence domain, then that set is a neighbourhood.

The neighbourhood is the cone of some string, and that string lies in the tagging, so the string begins with the boolean. The cone identity rewrites this cone as the tagging of the cone of the remaining suffix, injectivity of tagging makes the original set equal to that cone, and a cone is a neighbourhood.
ai-/
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
