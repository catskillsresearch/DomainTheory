module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326














theorem iTimes_isComputableMap :
    IsComputableMap prodUUPresentation UComputablePresentation iTimes :=
  (theorem_8_8_b_strong prodUUPresentation).choose_spec.choose_spec.2.2.1

end DomainTheory.NeighbourhoodSystems
