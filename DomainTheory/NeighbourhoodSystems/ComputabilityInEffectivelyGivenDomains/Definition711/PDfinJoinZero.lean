/-ai
The empty finite join in the power domain is the bottom element of the power domain.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710
public import Mathlib.Tactic
import all Mathlib.Tactic

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Definition 7.11 — the empty join.** With no arguments, `{ } = ⊥` (the least element of
`|ℙ𝒟|`). -/
def PDfinJoinZero : V.PowerDomain.Element := V.PowerDomain.bot

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
