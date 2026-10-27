module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.effectiveIso812d

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

section
/-- **`splitX812e`: the exercise's literal target split**, `U` as prober against `V`'s canonical
bisection. -/
noncomputable def splitX812e : Set ℚ → Set ℕ → Set ℚ → Set ℕ × Set ℕ :=
  ComputableBisection.splitFromBisection UComputablePresentation U_isComputableDiff B812e
    V_noMinimal
end

namespace isComputableSplit
open Domain.Recursive NeighborhoodSystem

section
/-- **Exercise 8.12(e), completed in full**: `splitX812e` satisfies `IsComputableSplit`.
`noncomputable def`, not `theorem` — `IsComputableSplit` is a data-carrying structure (its
`posIdx`/`negIdx` fields are `ℕ`-valued functions), mirroring `isComputableSplit.ofBisection`
itself (`(e)(c)(ii)`). -/
noncomputable def «812e» :
    IsComputableSplit UComputablePresentation VComputablePresentation splitX812e :=
  ComputableBisection.isComputableSplit.ofBisection UComputablePresentation U_isComputableDiff
    B812e V_noMinimal U_isPositive U_noMinimal U_diffClosed
end

end isComputableSplit

end DomainTheory.NeighbourhoodSystems
end
