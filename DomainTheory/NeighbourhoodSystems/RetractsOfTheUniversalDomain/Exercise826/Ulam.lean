module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

/-- **Self-abstraction inside `𝒰`** (the end-of-lecture equation `λx.τ ≅ i_→(λx.τ)`): given the
"outside" function `f : 𝒰 → 𝒰` (`τ`'s ordinary denotation as an approximable map), encode it into
`𝒰` via `i_→` (`iArrow`, Definition 8.9). -/
noncomputable def Ulam (f : ApproximableMap U U) : U.Element :=
  iArrow.toElementMap (toFilter f)

end DomainTheory.NeighbourhoodSystems
