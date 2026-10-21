/-ai
The inner cross of a binary operation at a fixed first argument and a list code is the fold of the inner step, with that argument as parameter and with accumulator zero, over the list code.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross.crossInnerStep

@[expose] public section

set_option linter.unusedSectionVars false

namespace Domain.Recursive

/-- `crossInner bop x c2` codes `[bop (x, y) ∣ y ∈ decodeList c2]` (up to order). -/
def crossInner (bop : ℕ → ℕ) (x c2 : ℕ) : ℕ := foldCode (crossInnerStep bop) x 0 c2

end Domain.Recursive
