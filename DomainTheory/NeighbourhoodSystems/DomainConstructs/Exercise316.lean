/-ai
The infinite iterate of a domain is isomorphic to the product of that domain with the iterate.

The numbered name example_316 is that statement.
ai-/
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
