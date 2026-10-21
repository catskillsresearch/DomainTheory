/-ai
Postcomposing the diagonal with the first projection returns the identity map.

The numbered name example_314 is that statement.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise314.proju2080_comp_diag

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_314.{u_1} : ∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
  @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α (Sum α α) α V
      (@DomainTheory.NeighbourhoodSystems.prod α α V V) V (@DomainTheory.NeighbourhoodSystems.proj₀ α α V V)
      (@DomainTheory.NeighbourhoodSystems.diag α V))
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α V) :=
  @DomainTheory.NeighbourhoodSystems.proj₀_comp_diag

end DomainTheory.NeighbourhoodSystems
