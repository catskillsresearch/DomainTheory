/-ai
The pair of 1 and 0 equals 1.

The equality is the definition of pairing.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem pair_one_zero : pair 1 0 = 1 := by simp [pair]

end DomainTheory.DataTypesAsLattices
