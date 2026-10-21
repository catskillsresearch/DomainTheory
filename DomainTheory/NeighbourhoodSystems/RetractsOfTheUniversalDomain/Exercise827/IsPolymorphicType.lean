/-ai
A polymorphic type is an approximable self-map d of the universal domain such that sub composed with d composed with sub equals d.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise826
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.subU

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

/-- **A polymorphic type** (Scott 1981, PRG-19, Exercise 8.27): `d = sub∘d∘sub`, `sub` here being
`subU` (Step 1's "`sub` regarded as a combinator on `𝒰`"). -/
def IsPolymorphicType (d : ApproximableMap U U) : Prop :=
  subU.comp (d.comp subU) = d

end DomainTheory.NeighbourhoodSystems
