/-ai
Scott 1976, (2.2): the minimal, or distributive, extension of a sequence at a set is the union of the values of the sequence at the indices that belong to the set.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.Comb
public import DomainTheory.DataTypesAsLattices.Lambda.mem_ofNat

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (2.2).** Minimal (distributive) extension `p̂(x) = ⋃ {p(n) | n ∈ x}`. -/
def minExtend (p : ℕ → Pomega) (x : Pomega) : Pomega :=
  ⋃ n ∈ x, p n

end DomainTheory.DataTypesAsLattices
