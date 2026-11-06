module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.diag

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

/-- Scott's Exercise 3.14: the first projection recovers the identity after the diagonal. -/
theorem example_314 :
    ∀ {α : Type*} (V : NeighborhoodSystem α),
      (proj₀ V V).comp (diag V) = idMap V :=
  @proj₀_comp_diag

end DomainTheory.NeighbourhoodSystems
