module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst36

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (4.22).** Evaluation combinator. -/
def evalC : Pomega :=
  graph (fun u => funOf (funOf u (ofNat 0)) (funOf u (ofNat 1)))

end DomainTheory.DataTypesAsLattices
