module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv.startFin
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv.stepFin

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability

open Sum Set

/-- The live-state `Finset` after reading `w` (mirrors `NFA.eval`, folding `stepFin` left to
right from `startFin`). -/
def evalFin (e : SExpr) (w : List Bool) : Finset (autState e) :=
  w.foldl (stepFin e) (startFin e)

end Exercise722

end DomainTheory.NeighbourhoodSystems
