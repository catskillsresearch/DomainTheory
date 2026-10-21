/-ai
The append of two list codes is the fold of the cons step, with parameter zero and with the second code as accumulator, over the first code.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross.consStep2

@[expose] public section

set_option linter.unusedSectionVars false

namespace Domain.Recursive

/-- `appendCode c1 c2` codes a list with the same **elements** as `decodeList c1 ++ decodeList c2`
(reversed on the `c1` side, since `foldCode` conses left-to-right; irrelevant for set-level uses). -/
def appendCode (c1 c2 : ℕ) : ℕ := foldCode consStep2 0 c2 c1

end Domain.Recursive
