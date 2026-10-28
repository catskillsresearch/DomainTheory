module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Udiff

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

noncomputable def splitX812e : Set ℚ → Set ℕ → Set ℚ → Set ℕ × Set ℕ :=
  ComputableBisection.splitFromBisection UComputablePresentation U_isComputableDiff B812e
    V.noMinimal

namespace isComputableSplit
open Domain.Recursive NeighborhoodSystem

noncomputable def «812e» :
    IsComputableSplit UComputablePresentation VComputablePresentation splitX812e :=
  ComputableBisection.isComputableSplit.ofBisection UComputablePresentation U_isComputableDiff
    B812e V.noMinimal U.isPositive U.noMinimal U.diffClosed

end isComputableSplit

end DomainTheory.NeighbourhoodSystems
end
