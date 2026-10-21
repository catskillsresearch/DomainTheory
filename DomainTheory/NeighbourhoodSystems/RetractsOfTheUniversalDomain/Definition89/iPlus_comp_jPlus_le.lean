/-ai
Applying the sum projection and then the sum embedding yields a self-map of the universal domain lying under the identity.

This inequality is the corresponding component of the projection pair chosen for the sum.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89.Basic

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88n.theorem_8_8_b_strong
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326


theorem iPlus_comp_jPlus_le : iPlus.comp jPlus ≤ idMap U :=
  (theorem_8_8_b_strong sumUUPresentation).choose_spec.choose_spec.2.1

end DomainTheory.NeighbourhoodSystems
