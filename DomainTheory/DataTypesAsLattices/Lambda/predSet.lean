/-ai
Scott 1976, Table 2: the predecessor of a set is the set of those n for which n + 1 belongs to the set.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, Table 2.** Predecessor `x − 1 = {n | n + 1 ∈ x}`. -/
def predSet (x : Pomega) : Pomega :=
  {k | k + 1 ∈ x}

end DomainTheory.DataTypesAsLattices
