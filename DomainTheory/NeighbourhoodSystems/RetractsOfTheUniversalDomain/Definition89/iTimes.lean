module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89.prodUUPresentation

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88n.theorem_8_8_b_strong
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

/-- **`i_× : 𝒰×𝒰 → 𝒰`** (Definition 8.9), fixed by `theorem_8_8_b_strong` applied to `𝒰×𝒰`. -/
noncomputable def iTimes : ApproximableMap (prod U U) U :=
  (theorem_8_8_b_strong prodUUPresentation).choose

end DomainTheory.NeighbourhoodSystems
