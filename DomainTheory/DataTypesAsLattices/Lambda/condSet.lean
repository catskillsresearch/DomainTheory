
module

public import DomainTheory.DataTypesAsLattices.Embedding

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, Table 2.** McCarthy conditional. -/
def condSet (z x y : Pomega) : Pomega :=
  {n | n ∈ x ∧ 0 ∈ z} ∪ {m | m ∈ y ∧ ∃ k, k + 1 ∈ z}

end DomainTheory.DataTypesAsLattices
