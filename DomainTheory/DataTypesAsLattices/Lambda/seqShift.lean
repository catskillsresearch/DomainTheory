module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.Comb
public import DomainTheory.DataTypesAsLattices.Lambda.mem_ofNat
public import DomainTheory.DataTypesAsLattices.Lambda.seqFun

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- Shift of a sequence: `(λt. u_{t+1})`. -/
def seqShift (u : Pomega) : Pomega :=
  graph (fun z => seqFun u (succSet z))

end DomainTheory.DataTypesAsLattices
