/-ai
stepFin is the finite set of states reached in one step from a finite set of states on one symbol. It is the bounded union of the single-state finite steps.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv.stepFinSingle

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability

open Sum Set

/-- The `Finset`-lifted step (mirrors `NFA.stepSet`). -/
def stepFin (e : SExpr) (S : Finset (autState e)) (c : Bool) : Finset (autState e) :=
  S.biUnion (fun s => stepFinSingle e s c)

end Exercise722

end DomainTheory.NeighbourhoodSystems
