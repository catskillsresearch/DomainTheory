/-ai
Scott's Table 2 defines the McCarthy conditional of z, x, and y to be the union of those members of x for which 0 lies in z and those members of y for which some successor lies in z.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Embedding

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, Table 2.** McCarthy conditional. -/
def condSet (z x y : Pomega) : Pomega :=
  {n | n ∈ x ∧ 0 ∈ z} ∪ {m | m ∈ y ∧ ∃ k, k + 1 ∈ z}

end DomainTheory.DataTypesAsLattices
