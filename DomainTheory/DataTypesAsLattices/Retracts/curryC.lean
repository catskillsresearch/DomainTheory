module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.pairSeq
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst36

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (4.23).** Currying combinator. -/
def curryC : Pomega :=
  graph (fun u => graph (fun x => graph (fun y => funOf u (pairSeq x y))))

end DomainTheory.DataTypesAsLattices
