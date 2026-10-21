/-ai
The distributive extension of primitive recursion at a base value, a step, and an argument set is the union of the primitive-recursive values at the indices that belong to the argument.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.Comb
public import DomainTheory.DataTypesAsLattices.Lambda.mem_ofNat
public import DomainTheory.DataTypesAsLattices.Lambda.primRecVal

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def primRecHat (a f x : Pomega) : Pomega :=
  ⋃ n ∈ x, primRecVal a f n

end DomainTheory.DataTypesAsLattices
