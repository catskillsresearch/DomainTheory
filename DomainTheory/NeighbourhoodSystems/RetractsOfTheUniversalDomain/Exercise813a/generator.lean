/-ai
The i-th generator is the set of natural numbers whose i-th binary digit is 1.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812g4
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a.GeneratedBy
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a.testBit_bitmaskOf

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

/-- The **`i`-th generator**: `{n | n.testBit i}`, the set of naturals whose `i`-th binary digit is
`1`. These are Scott's `ℵ₀` propositional variables, realized concretely. -/
def generator (i : ℕ) : Set ℕ := {n : ℕ | n.testBit i = true}

end DomainTheory.NeighbourhoodSystems
