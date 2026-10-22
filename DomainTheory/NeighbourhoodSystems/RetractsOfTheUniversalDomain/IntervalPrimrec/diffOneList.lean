module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.decodeRatPair_encodeRatPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.decodeQPairList_encodeQPairList

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

/-- **Difference of a single interval-pair by another**, as a `≤ 2`-element list, via the
unconditional `Ico_diff_Ico`. -/
def diffOneList (p q : ℚ × ℚ) : List (ℚ × ℚ) := [(p.1, p.2 ⊓ q.1), (p.1 ⊔ q.2, p.2)]

end DomainTheory.NeighbourhoodSystems
