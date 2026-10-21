/-ai
The body of the term-level dollar step at s, u, and z is the conditional on z whose then-branch is the application of u to the numeral 0 and whose else-branch is the application of s, applied to the term shift of u, to the predecessor of z.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.Comb
public import DomainTheory.DataTypesAsLattices.Lambda.mem_ofNat
public import DomainTheory.DataTypesAsLattices.Lambda.termShift

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def termDollarStepBody (s u z : Pomega) : Pomega :=
  condSet z (funOf u (ofNat 0))
    (funOf (funOf s (termShift u)) (predSet z))

end DomainTheory.DataTypesAsLattices
