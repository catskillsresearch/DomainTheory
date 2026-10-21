/-ai
Scott's integer convention takes the numeral n to be the singleton whose only member is n, as an element of Pω.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- Scott's integer convention: `n = {n}` as an element of `Pω`. -/
def ofNat (n : ℕ) : Pomega := {n}

end DomainTheory.DataTypesAsLattices
