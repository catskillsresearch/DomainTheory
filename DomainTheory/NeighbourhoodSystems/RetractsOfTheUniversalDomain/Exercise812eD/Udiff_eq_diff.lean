module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitV
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812eD.Udiff

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **`Udiff` realizes set difference at the raw (uncanonicalized) `presentedIntervals` level**,
unconditionally — the one respect in which `\` is *simpler* than `∩` here (no consistency case
split needed at this stage). -/
theorem Udiff_eq_diff (n m : ℕ) :
    presentedIntervals (decodeQPairList (Udiff n m)) = UX n \ UX m := by
  unfold Udiff
  exact presentedIntervals_decodeQPairList_diffCode (canonCode n) (canonCode m)

end DomainTheory.NeighbourhoodSystems
