/-ai
The product of every d, regarded as a self-map of the universal domain, is a projection.

Conjugate the projection on the function space through i-arrow and j-arrow.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise826
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.isProjection_piD

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap
































/-- **`Π(d)`, regarded as living in `𝒰` (`piU d`), is a projection, for every `d`.** Half of "for
`d` a polymorphic type, `Π(d)` is a type" (Definition 8.3's `IsProjection` clause) — Scott's own
"it is easy to check" — obtained "for free" from `isProjection_piD` via the same conjugation
gadget (`isProjection_conjArrow`) used for `subU` in Step 1. Note this does not even need `d` to
be a polymorphic type. -/
theorem isProjection_piU (d : ApproximableMap U U) : IsProjection (piU d) :=
  isProjection_conjArrow (isProjection_piD d)

end DomainTheory.NeighbourhoodSystems
