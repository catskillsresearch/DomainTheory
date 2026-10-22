module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise826
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.piD

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

/-- **`Π(d)`, regarded as a combinator living in `𝒰` itself** — conjugating `piD d` through
`i_→, j_→` (Definition 8.9), exactly as `subU` was built from `subApprox` in Step 1. This is what
Scott's "type" means: a self-map *of `𝒰`*, not of `(𝒰→𝒰)`. -/
noncomputable def piU (d : ApproximableMap U U) : ApproximableMap U U :=
  iArrow.comp ((piD d).comp jArrow)

end DomainTheory.NeighbourhoodSystems
