/-ai
One decoded presentation is contained in another if and only if the presentation of their difference code is empty.

Rewrite by the presentation of the difference code, by emptiness of a set that fails to be nonempty, and by emptiness of a set difference.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive








































/-- **Subset between `presentedIntervals`-coded sets reduces to non-emptiness of `diffCode`.** -/
theorem presentedIntervals_decodeQPairList_subset_iff (c1 c2 : ℕ) :
    presentedIntervals (decodeQPairList c1) ⊆ presentedIntervals (decodeQPairList c2) ↔
      ¬ (presentedIntervals (decodeQPairList (diffCode c1 c2))).Nonempty := by
  rw [presentedIntervals_decodeQPairList_diffCode, Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty]

end DomainTheory.NeighbourhoodSystems
