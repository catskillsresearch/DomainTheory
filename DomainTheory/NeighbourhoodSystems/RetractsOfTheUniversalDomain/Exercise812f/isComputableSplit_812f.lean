module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.VDiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812f.splitX812f

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **Exercise 8.12(f), completed in full**: `splitX812f` satisfies `IsComputableSplit`, the
mirror image of `Exercise812eD.lean`'s `isComputableSplit_812e`. `noncomputable def`, not
`theorem` — `IsComputableSplit` is a data-carrying structure (its `posIdx`/`negIdx` fields are
`ℕ`-valued functions), exactly as `isComputableSplit_812e` itself. -/
noncomputable def isComputableSplit_812f :
    IsComputableSplit VComputablePresentation UComputablePresentation splitX812f :=
  ComputableBisection.isComputableSplit_ofBisection VComputablePresentation V_isComputableDiff
    UBisection2 U_noMinimal V_isPositive V_noMinimal V_diffClosed

end DomainTheory.NeighbourhoodSystems
