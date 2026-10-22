module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise826
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.subU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.BasicInst38

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

/-- **The "type at `s`" map**, `decode(subU(d(s)))`, as a function of the *element* `s` (not just
`s = subU(principal Y)` for some `Y`). Packaging `piDApply`'s inner formula this way is what lets
continuity/monotonicity in `s` be stated directly. -/
noncomputable def piDTypeMap (d : ApproximableMap U U) : ApproximableMap U (funSpace U U) :=
  jArrow.comp (subU.comp d)

end DomainTheory.NeighbourhoodSystems
