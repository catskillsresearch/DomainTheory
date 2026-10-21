/-ai
The fixed projection from the universal domain onto the function space of the universal domain with itself is the second component of the projection pair chosen with the function-space embedding.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89.funSpaceUUPresentation

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88n.theorem_8_8_b_strong
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

/-- **`j_→ : 𝒰 → (𝒰→𝒰)`** (Definition 8.9). -/
noncomputable def jArrow : ApproximableMap U (funSpace U U) :=
  (theorem_8_8_b_strong funSpaceUUPresentation).choose_spec.choose

end DomainTheory.NeighbourhoodSystems
