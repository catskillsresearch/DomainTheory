module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.effectiveIso812d

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

/-- **`splitX812e`: the exercise's literal target split**, `U` as prober against `V`'s canonical
bisection. -/
noncomputable def splitX812e : Set ℚ → Set ℕ → Set ℚ → Set ℕ × Set ℕ :=
  ComputableBisection.splitFromBisection UComputablePresentation U_isComputableDiff B812e
    V.noMinimal

namespace isComputableSplit
open Domain.Recursive NeighborhoodSystem

/-- **Exercise 8.12(e), completed in full**: `splitX812e` satisfies `IsComputableSplit`.
`noncomputable def`, not `theorem` — `IsComputableSplit` is a data-carrying structure (its
`posIdx`/`negIdx` fields are `ℕ`-valued functions), mirroring `isComputableSplit.ofBisection`
itself (`(e)(c)(ii)`). -/
noncomputable def «812e» :
    IsComputableSplit UComputablePresentation VComputablePresentation splitX812e :=
  ComputableBisection.isComputableSplit.ofBisection UComputablePresentation U_isComputableDiff
    B812e V.noMinimal U.isPositive U.noMinimal U.diffClosed

end isComputableSplit

end DomainTheory.NeighbourhoodSystems
end
