module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.powerDomainEffective

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.NeighborhoodSystem
open NeighborhoodSystem

/-- Scott's Proposition 7.10: the powerdomain of an effectively given system is effectively given. -/
theorem proposition_710 :
    ∀ {α : Type*} {V : NeighborhoodSystem α},
      V.IsEffectivelyGiven → V.PowerDomain.IsEffectivelyGiven :=
  @PowerDomain_isEffectivelyGiven

end DomainTheory.NeighbourhoodSystems.NeighborhoodSystem
