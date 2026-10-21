/-ai
The elements of the binary-sequence domain are order-isomorphic to the elements of the sum of that domain with itself, by the map into the sum and the map back from the sum, with the two round trips given by the corresponding inverse lemmas. One element lies below another if and only if the images do: a neighbourhood of the domain is the master or a single-bit tagging, and membership of the corresponding injected neighbourhood transfers along the order of the images, while a neighbourhood of the sum is the master or one of the two injections and transfers back by the same classification.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.mem_embBit
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.memB_cases
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.BB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.toBB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.toBB_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.toBB_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.fromBB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.fromBB_mem_embF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.fromBB_mem_embT
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.fromBB_toBB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.toBB_fromBB

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

/-- **Example 6.2 (Scott 1981, PRG-19) — the isomorphism `|B| ≃o |B + B|`.** -/
def bbEquiv : B.Element ≃o BB.Element where
  toFun := toBB
  invFun := fromBB
  left_inv := fromBB_toBB
  right_inv := toBB_fromBB
  map_rel_iff' := by
    intro x x'
    constructor
    · intro h X hX
      rcases memB_cases (x.sub hX) with rfl | ⟨A, hA, rfl⟩ | ⟨A, hA, rfl⟩
      · exact x'.master_mem
      · exact (toBB_mem_inj₀ hA).mp (h _ (Or.inr (Or.inl ⟨A, hA, rfl, hX⟩)))
      · exact (toBB_mem_inj₁ hA).mp (h _ (Or.inr (Or.inr ⟨A, hA, rfl, hX⟩)))
    · intro h W hW
      rcases hW with rfl | ⟨X, hX, rfl, hzX⟩ | ⟨Y, hY, rfl, hzY⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨X, hX, rfl, h _ hzX⟩)
      · exact Or.inr (Or.inr ⟨Y, hY, rfl, h _ hzY⟩)

end Example62

end DomainTheory.NeighbourhoodSystems
