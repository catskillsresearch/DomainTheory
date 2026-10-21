/-ai
The domain of the joint evaluator is the product of the function space of the universal domain with itself and the product of that function space with the universal domain. An element packages the varying map, the curry variable, and the point.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Pow
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Embed
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Closing
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise820

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

/-- The domain `(𝒰→𝒰) × ((𝒰→𝒰) × 𝒰)` of the joint evaluator: an element `⟨ψ, ⟨φ, x⟩⟩` packages
the varying map `ψ` (to become `a`), the curry variable `φ`, and the point `x`. -/
abbrev RDom := prod (funSpace U U) (prod (funSpace U U) U)

end DomainTheory.NeighbourhoodSystems
