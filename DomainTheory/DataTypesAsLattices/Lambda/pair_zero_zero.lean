/-ai
The pair of 0 and 0 equals 0.

The equality is the definition of pairing.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem pair_zero_zero : pair 0 0 = 0 := by simp [pair]
end DomainTheory.DataTypesAsLattices
