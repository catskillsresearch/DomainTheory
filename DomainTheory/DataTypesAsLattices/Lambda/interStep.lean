/-ai
The least operator solving the (2.17) recursion sends a functional to the graph of the map which, at each first argument, is the graph of the conditional returning zero when both arguments are zero and otherwise the successor of the functional applied to the two predecessors.
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

/-- Least operator solving the (2.17) recursion. -/
def interStep (f : Pomega) : Pomega :=
  graph (fun x => graph (fun y =>
    condSet x (condSet y (ofNat 0) botElem)
      (succSet (funOf (funOf f (predSet x)) (predSet y)))))

end DomainTheory.DataTypesAsLattices
