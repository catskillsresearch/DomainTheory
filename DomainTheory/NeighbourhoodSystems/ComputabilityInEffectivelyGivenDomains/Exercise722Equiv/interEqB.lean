module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv.subsetB

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability

open Sum Set

/-- **Exercise 7.22k.** Relation (i) on `SExpr` syntax — language equivalence — decided by
`subsetB` in both directions. -/
def interEqB (e1 e2 : SExpr) : Bool := subsetB e1 e2 && subsetB e2 e1

end Exercise722

end DomainTheory.NeighbourhoodSystems
