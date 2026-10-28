module

public import DomainTheory.DataTypesAsLattices.Graph.lam
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Enumeration.Avoids
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Lambda.envSet
public import DomainTheory.DataTypesAsLattices.Lambda.interp
public import DomainTheory.DataTypesAsLattices.Lambda.termShift
public import DomainTheory.DataTypesAsLattices.Lambda.termDollarStepBody
public import DomainTheory.DataTypesAsLattices.Lambda.termDollarStep
public import DomainTheory.DataTypesAsLattices.Lambda.condSet
public import DomainTheory.DataTypesAsLattices.Lambda.succSet

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def dollarStepTerm : Term :=
  .lam 0 (.lam 1 (.lam 2
    (.cond (.var 2)
      (.app (.var 1) .zero)
      (.app (.app (.var 0) (.lam 3 (.app (.var 1) (.succ (.var 3)))))
        (.pred (.var 2))))))

namespace dollarStepTerm

theorem interp :
    interp dollarStepTerm (fun _ => botElem) = graph termDollarStep := by
  unfold dollarStepTerm termDollarStep termDollarStepBody termShift DomainTheory.DataTypesAsLattices.interp
  apply congrArg graph
  funext s
  simp only[envSet]
  apply congrArg graph
  funext u
  simp only[envSet]
  apply congrArg graph
  funext z
  simp[envSet, condSet, succSet]
  rfl

end dollarStepTerm

end DomainTheory.DataTypesAsLattices
