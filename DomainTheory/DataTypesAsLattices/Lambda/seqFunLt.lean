/-ai
A finite stage of the dollar iteration, at a strict bound, is the union of the applications of the functional to the numeral of each index that belongs to the argument and lies strictly below the bound.
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

/-- Finite stage of the `$` iteration: `⋃ { uᵢ | i ∈ x, i < n }`. -/
def seqFunLt (u x : Pomega) (n : ℕ) : Pomega :=
  ⋃ i ∈ x, ⋃ _ : i < n, funOf u (ofNat i)

end DomainTheory.DataTypesAsLattices
