/-ai
Folding the single-interval difference across a list of rational pairs removes, from the
set presented by the accumulator, the set presented by that list.

The proof is by induction on the list. The empty list simplifies. For a cons cell, the
fold equation, the inductive hypothesis at the accumulator updated by one difference,
the single-difference and cons lemmas for presented intervals, and the double
set-difference identity give the claim.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive


theorem presentedIntervals_foldl_diffSingleList (L2 : List (ℚ × ℚ)) :
    ∀ acc : List (ℚ × ℚ),
      presentedIntervals (L2.foldl diffSingleList acc) = presentedIntervals acc \ presentedIntervals L2 := by
  induction L2 with
  | nil => intro acc; simp
  | cons a l ih =>
    intro acc
    rw [List.foldl_cons, ih (diffSingleList acc a), presentedIntervals_diffSingleList,
      presentedIntervals_cons, Set.sdiff_sdiff]

end DomainTheory.NeighbourhoodSystems
