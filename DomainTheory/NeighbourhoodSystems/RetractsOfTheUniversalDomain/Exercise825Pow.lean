/-ai
For any domain, the product of its infinite power with itself is isomorphic to that infinite power. Specialized to the universal domain, this is Scott's isomorphism of the infinite power with its product.

The numbered name example_825_pow is that statement.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Pow.pow_prod_isomorphic

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_825_pow.{u_1} : ∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
  @DomainTheory.NeighbourhoodSystems.Isomorphic (Sum (Prod Nat α) (Prod Nat α)) (Prod Nat α)
    (@DomainTheory.NeighbourhoodSystems.prod (Prod Nat α) (Prod Nat α) (@DomainTheory.NeighbourhoodSystems.iterSys α V)
      (@DomainTheory.NeighbourhoodSystems.iterSys α V))
    (@DomainTheory.NeighbourhoodSystems.iterSys α V) :=
  @DomainTheory.NeighbourhoodSystems.pow_prod_isomorphic

end DomainTheory.NeighbourhoodSystems
