/-ai
The singleton join of an element x is the finite join of the length-one family whose only value is x.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition711.PDfinJoin
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition711.PDmem_finJoinZero

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Definition 7.11 — singleton join.** Write `{x}` for the unary join. -/
def PDsingleton (x : V.Element) : V.PowerDomain.Element := V.PDfinJoin 1 (fun (_ : Fin 1) => x)

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
