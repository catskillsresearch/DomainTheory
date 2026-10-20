module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62

namespace Exercise822

/-- `C` is positive: every `C`-neighbourhood (a cone or a singleton) is nonempty. -/
theorem C_nonempty : ∀ X, C.mem X → X.Nonempty := by
  rintro X (⟨σ, rfl⟩ | ⟨σ, rfl⟩)
  · exact ⟨σ, List.prefix_rfl⟩
  · exact ⟨σ, rfl⟩

end Exercise822

end DomainTheory.NeighbourhoodSystems
