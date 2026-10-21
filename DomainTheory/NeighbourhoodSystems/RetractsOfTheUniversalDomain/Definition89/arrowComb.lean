/-ai
The function-space combinator of two self-maps of the universal domain is the function-space embedding composed after the lambda combinator of the two maps composed after the function-space projection.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89.iArrow
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89.jArrow
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89.lamComb

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

/-- **`a → b : 𝒰 → 𝒰`** (Definition 8.9): `i_→ ∘ (λf. b∘f∘a) ∘ j_→`. -/
noncomputable def arrowComb (a b : ApproximableMap U U) : ApproximableMap U U :=
  iArrow.comp ((lamComb a b).comp jArrow)

end DomainTheory.NeighbourhoodSystems
