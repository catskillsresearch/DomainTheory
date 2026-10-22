
module

public import DomainTheory.DataTypesAsLattices.Continuous

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, §1, Definition.**
`graph(f) = {(n, m) | m ∈ f(e n)}`. -/
def graph (f : Pomega → Pomega) : Pomega :=
  {p | ∃ n m, p = pair n m ∧ m ∈ f (e n)}

end DomainTheory.DataTypesAsLattices
