module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326


section General

variable {α β γ δ : Type*}

/-- **`TD.bot = Example23.botElt`.** These are the *same* element (`TD` and `Example23.T` are both
`Example12.neighborhoodSystem`), but not syntactically unifiable by `rfl` (the `abbrev`s don't
delta-reduce transparently through `NeighborhoodSystem.bot`'s field projection), so we prove it by
antisymmetry instead. -/
theorem TD_bot_eq_botElt : TD.bot = Example23.botElt :=
  le_antisymm (NeighborhoodSystem.bot_le _ _) (Example23.botElt_le _)

end General
end DomainTheory.NeighbourhoodSystems
