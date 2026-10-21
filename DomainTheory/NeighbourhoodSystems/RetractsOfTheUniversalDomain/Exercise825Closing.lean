/-ai
An isomorphism of a domain D with the function space into a domain V, together with an isomorphism of the product of V with itself with V, yields an isomorphism of D with its own function space.

The numbered name example_825_closing is that statement.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Closing.funSpace_self_isomorphic

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_825_closing.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} {D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
  {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β},
  @DomainTheory.NeighbourhoodSystems.Isomorphic α (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β D V) D
      (@DomainTheory.NeighbourhoodSystems.funSpace α β D V) →
    @DomainTheory.NeighbourhoodSystems.Isomorphic (Sum β β) β (@DomainTheory.NeighbourhoodSystems.prod β β V V) V →
      @DomainTheory.NeighbourhoodSystems.Isomorphic α (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α D D) D
        (@DomainTheory.NeighbourhoodSystems.funSpace α α D D) :=
  @DomainTheory.NeighbourhoodSystems.funSpace_self_isomorphic

end DomainTheory.NeighbourhoodSystems
