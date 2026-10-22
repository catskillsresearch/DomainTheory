module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324Iter.funIter_isomorphic

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_324_iter.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
  {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β},
  @DomainTheory.NeighbourhoodSystems.Isomorphic
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap α (Prod Nat β) V₀
      (@DomainTheory.NeighbourhoodSystems.iterSys β V₁))
    (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁))
    (@DomainTheory.NeighbourhoodSystems.funSpace α (Prod Nat β) V₀ (@DomainTheory.NeighbourhoodSystems.iterSys β V₁))
    (@DomainTheory.NeighbourhoodSystems.iterSys (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
      (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁)) :=
  @DomainTheory.NeighbourhoodSystems.funIter_isomorphic

end DomainTheory.NeighbourhoodSystems
