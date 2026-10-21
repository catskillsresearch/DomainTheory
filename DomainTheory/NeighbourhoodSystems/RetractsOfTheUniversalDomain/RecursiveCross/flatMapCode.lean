/-ai
flatMapCode f x c is the list code of the flat map of the decoded list of c under y mapped to the decoded list of f of the pair of x and y, up to order and duplicates. It is the fold of flatMapStep f, with x held fixed and with empty accumulator.
ai-/
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
