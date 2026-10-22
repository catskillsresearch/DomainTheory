module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.NeighborhoodSystemu2ePowerDomain_isEffectivelyGiven

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.NeighborhoodSystem

set_option linter.unusedVariables false

theorem theorem_710.{u_1} : ∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α},
  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven α V →
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven (Set α)
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V) :=
  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain_isEffectivelyGiven

end DomainTheory.NeighbourhoodSystems.NeighborhoodSystem
