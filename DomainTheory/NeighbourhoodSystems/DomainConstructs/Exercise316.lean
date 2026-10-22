module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.iter_isomorphic

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_316.{u_1} : ∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
  @DomainTheory.NeighbourhoodSystems.Isomorphic (Prod Nat α) (Sum α (Prod Nat α))
    (@DomainTheory.NeighbourhoodSystems.iterSys α V)
    (@DomainTheory.NeighbourhoodSystems.prod α (Prod Nat α) V (@DomainTheory.NeighbourhoodSystems.iterSys α V)) :=
  @DomainTheory.NeighbourhoodSystems.iter_isomorphic

end DomainTheory.NeighbourhoodSystems
