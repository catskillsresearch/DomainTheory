/-ai
The neighbourhood systems U and V of Exercise 8.12 are effectively isomorphic. The isomorphism is assembled from their computable presentations, their computable differences and unions, the two computable splitting operations and their specifications, positivity, closure under difference, absence of minimal neighbourhoods, the nonempty masters, and the zero neighbourhoods.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812eD
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812f
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812g1a
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812g1b
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812g2

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem Exercise718

/-- **Exercise 8.12, completed in full**: `U` and `V` are effectively isomorphic
neighbourhood systems. -/
noncomputable def effectiveIso812_UV : EffectiveIso UComputablePresentation VComputablePresentation :=
  effectiveIso812d UComputablePresentation VComputablePresentation U_isComputableDiff
    V_isComputableDiff splitX812e isComputableSplit_812e splitX812f isComputableSplit_812f
    U_isPositive U_diffClosed U_noMinimal hxSplit812e V_isPositive V_diffClosed V_noMinimal
    hySplit812f U_master_nonempty V_master_nonempty U_isComputableUnion V_isComputableUnion UX_zero
    VX_zero

end DomainTheory.NeighbourhoodSystems
