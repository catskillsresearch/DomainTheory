/-ai
Scott's section 1 defines the graph of a map f to be the set of pairs of n and m such that m lies in f at the basic element coded by n.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Continuous

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, §1, Definition.**
`graph(f) = {(n, m) | m ∈ f(e n)}`. -/
def graph (f : Pomega → Pomega) : Pomega :=
  {p | ∃ n m, p = pair n m ∧ m ∈ f (e n)}

end DomainTheory.DataTypesAsLattices
