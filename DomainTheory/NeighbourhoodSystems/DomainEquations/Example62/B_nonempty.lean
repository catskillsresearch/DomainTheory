module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.mem_embBit

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

/-- Scott's standing assumption `∅ ∉ B`: every neighbourhood of `B` is nonempty (cones contain their
generating prefix). -/
theorem B_nonempty : ∀ X, B.mem X → X.Nonempty := by
  rintro X ⟨σ, rfl⟩; exact ⟨σ, List.prefix_rfl⟩

end Example62

end DomainTheory.NeighbourhoodSystems
