module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv.stepFinSingle

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability

open Sum Set

/-- The `Finset`-lifted step (mirrors `NFA.stepSet`). -/
def stepFin (e : SExpr) (S : Finset (autState e)) (c : Bool) : Finset (autState e) :=
  S.biUnion (fun s => stepFinSingle e s c)

end Exercise722

end DomainTheory.NeighbourhoodSystems
