module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

/-- **`λf. b∘f∘a : (𝒰→𝒰) → (𝒰→𝒰)`**, uncurried as `b ∘ eval ∘ (id ×ₘ a)`. -/
noncomputable def lamComb (a b : ApproximableMap U U) :
    ApproximableMap (funSpace U U) (funSpace U U) :=
  curry (b.comp ((evalMap U U).comp (prodMap (idMap (funSpace U U)) a)))

end DomainTheory.NeighbourhoodSystems
