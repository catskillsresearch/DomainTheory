module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.Comb
public import DomainTheory.DataTypesAsLattices.Lambda.mem_ofNat
public import DomainTheory.DataTypesAsLattices.Lambda.termShift

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

def termDollarStepBody (s u z : Pomega) : Pomega :=
  condSet z (funOf u (ofNat 0))
    (funOf (funOf s (termShift u)) (predSet z))

end DomainTheory.DataTypesAsLattices
