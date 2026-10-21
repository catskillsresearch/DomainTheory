/-ai
Proposition 7.10. The Smyth power domain of an effectively given neighbourhood system is effectively given. The consistency decider is taken from the given presentation inside the existence proof.

The numbered name theorem_710 is that statement.
ai-/
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
