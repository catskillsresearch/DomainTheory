module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89.iTimes
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89.jTimes

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

/-- **`a × b : 𝒰 → 𝒰`** (Definition 8.9): `i_× ∘ ⟨a∘proj₀, b∘proj₁⟩ ∘ j_×`. -/
noncomputable def prodComb (a b : ApproximableMap U U) : ApproximableMap U U :=
  iTimes.comp ((paired (a.comp (proj₀ U U)) (b.comp (proj₁ U U))).comp jTimes)

end DomainTheory.NeighbourhoodSystems
