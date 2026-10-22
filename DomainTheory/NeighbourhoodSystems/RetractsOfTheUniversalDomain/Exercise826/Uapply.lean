module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

/-- **Self-application inside `𝒰`** (the end-of-lecture equation `u(x) := j_→(u)(x)`): decode
`u : 𝒰` into an actual function `𝒰 → 𝒰` via `j_→` (`jArrow`, Definition 8.9), then apply it to
`x`. -/
noncomputable def Uapply (u x : U.Element) : U.Element :=
  (evalMap U U).toElementMap (pair (jArrow.toElementMap u) x)

end DomainTheory.NeighbourhoodSystems
