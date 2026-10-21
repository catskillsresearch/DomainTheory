/-ai
Subtracting one list of rational pairs from another presents the difference of the two presented sets.

The empty list simplifies. For a cons cell, the concatenation of the whole-pair difference with the difference of the tail, the append presentation, the whole-pair presentation, the inductive hypothesis, and the cons presentation law match the distribution of set difference over union.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.presentedIntervals_diffAllList

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive


theorem presentedIntervals_diffLists (L1 L2 : List (ℚ × ℚ)) :
    presentedIntervals (diffLists L1 L2) = presentedIntervals L1 \ presentedIntervals L2 := by
  induction L1 with
  | nil => simp [diffLists]
  | cons a l ih =>
    rw [show diffLists (a :: l) L2 = diffAllList a L2 ++ diffLists l L2 from rfl,
      presentedIntervals_append, presentedIntervals_diffAllList, ih, presentedIntervals_cons,
      Set.union_sdiff_distrib]

end DomainTheory.NeighbourhoodSystems
