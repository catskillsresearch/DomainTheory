/-ai
The code that subtracts the rational-pair list coded by one natural from the list coded by another is the flat map that sends each argument to the whole-list difference of its two unpaired components, with the subtracted list as the parameter.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.decodeRatPair_encodeRatPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.decodeQPairList_encodeQPairList
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.diffAllCode

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

/-- `diffCode c1 c2` subtracts the QPair-list coded by `c2` from the QPair-list coded by `c1`. -/
def diffCode (c1 c2 : ℕ) : ℕ := flatMapCode (fun t => diffAllCode t.unpair.2 t.unpair.1) c2 c1

end DomainTheory.NeighbourhoodSystems
