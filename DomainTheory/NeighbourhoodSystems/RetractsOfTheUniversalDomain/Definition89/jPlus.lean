module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89.U_mem_nonempty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89.sumUUPresentation

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88n.theorem_8_8_b_strong
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

/-- **`j₊ : 𝒰 → 𝒰+𝒰`** (Definition 8.9). -/
noncomputable def jPlus : ApproximableMap U (sum U U U_mem_nonempty U_mem_nonempty) :=
  (theorem_8_8_b_strong sumUUPresentation).choose_spec.choose

end DomainTheory.NeighbourhoodSystems
