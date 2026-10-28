module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Graph.lam
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Lambda.envSet
public import DomainTheory.DataTypesAsLattices.Lambda.interStep
public import DomainTheory.DataTypesAsLattices.Lambda.interp
public import DomainTheory.DataTypesAsLattices.Enumeration.Avoids
public import DomainTheory.DataTypesAsLattices.Lambda.eq_2_14

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

def interStepTerm : Term :=
  let omega : Term := .lam 4 (.app (.var 4) (.var 4))
  .lam 0 (.lam 1 (.lam 2
    (.cond (.var 1)
      (.cond (.var 2) .zero (.app omega omega))
      (.succ (.app (.app (.var 0) (.pred (.var 1))) (.pred (.var 2)))))))

namespace interStepTerm

theorem interp :
    interp interStepTerm (fun _ => botElem) = graph interStep := by
  unfold interStepTerm interStep
  simp only[_root_.DomainTheory.DataTypesAsLattices.interp, envSet, Function.update_self]
  apply congrArg graph
  funext f
  apply congrArg graph
  funext x
  apply congrArg graph
  funext y
  congr 2
  exact _root_.DomainTheory.DataTypesAsLattices.eq_2_14

end interStepTerm

end DomainTheory.DataTypesAsLattices
