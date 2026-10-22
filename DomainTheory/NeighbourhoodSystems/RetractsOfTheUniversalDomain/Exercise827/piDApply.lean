module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise826
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.subU

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

/-- **`Π(d)(x)`, for `x` a plain map `𝒰 → 𝒰`** (not yet an element of the function space) — the
formula's "closed form" as a composite `ApproximableMap`, matching Scott's
`λt. sub(d(sub(t)))(x(sub(t)))` literally. -/
noncomputable def piDApply (d f : ApproximableMap U U) : ApproximableMap U U :=
  (evalMap U U).comp (paired (jArrow.comp (subU.comp (d.comp subU))) (f.comp subU))

end DomainTheory.NeighbourhoodSystems
