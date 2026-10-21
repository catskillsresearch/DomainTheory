/-ai
The product combinator of two self-maps of the universal domain is the product embedding composed after the pairing of the first map after the left projection with the second map after the right projection, composed after the product projection.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89.iTimes
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89.jTimes

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

/-- **`a × b : 𝒰 → 𝒰`** (Definition 8.9): `i_× ∘ ⟨a∘proj₀, b∘proj₁⟩ ∘ j_×`. -/
noncomputable def prodComb (a b : ApproximableMap U U) : ApproximableMap U U :=
  iTimes.comp ((paired (a.comp (proj₀ U U)) (b.comp (proj₁ U U))).comp jTimes)

end DomainTheory.NeighbourhoodSystems
