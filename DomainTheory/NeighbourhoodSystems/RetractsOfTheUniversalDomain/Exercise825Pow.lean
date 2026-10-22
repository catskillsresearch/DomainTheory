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
