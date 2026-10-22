module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.recDecidableu2082_presentedIntervals_subset

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive


/-- **Equality between `presentedIntervals`-coded sets is recursively decidable**, from
`recDecidable₂_presentedIntervals_subset` in both directions (`Set.Subset.antisymm_iff`). -/
theorem recDecidable₂_presentedIntervals_eq :
    RecDecidable₂ (fun c1 c2 =>
      presentedIntervals (decodeQPairList c1) = presentedIntervals (decodeQPairList c2)) := by
  unfold RecDecidable₂
  refine RecDecidable.of_iff (fun t => ?_)
    (recDecidable₂_presentedIntervals_subset.and recDecidable₂_presentedIntervals_subset.swap)
  exact Set.Subset.antisymm_iff

end DomainTheory.NeighbourhoodSystems
