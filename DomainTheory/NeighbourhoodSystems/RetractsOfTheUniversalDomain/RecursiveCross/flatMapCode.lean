module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross.flatMapStep

@[expose] public section

set_option linter.unusedSectionVars false

namespace Domain.Recursive

/-- **`flatMapCode f x c`** codes `(decodeList c).flatMap (fun y => decodeList (f (pair x y)))`
(up to order/duplicates). -/
def flatMapCode (f : ℕ → ℕ) (x c : ℕ) : ℕ := foldCode (flatMapStep f) x 0 c

end Domain.Recursive
