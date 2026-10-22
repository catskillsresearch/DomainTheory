module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.mem_decodeQPairList_combineCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.mem_combineIntervals

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive


/-- **`combineCode` realizes `combineIntervals` at the set level.** -/
theorem presentedIntervals_decodeQPairList_combineCode (c1 c2 : ℕ) :
    presentedIntervals (decodeQPairList (combineCode c1 c2))
      = presentedIntervals (decodeQPairList c1) ∩ presentedIntervals (decodeQPairList c2) := by
  rw [presentedIntervals_inter]
  apply presentedIntervals_congr
  intro p
  rw [mem_decodeQPairList_combineCode, mem_combineIntervals]

end DomainTheory.NeighbourhoodSystems
