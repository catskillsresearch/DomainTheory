/-ai
Interpreting the dollar step term in the bottom environment yields the graph of the term's functional.

Unfolding the term, the functional, its body, the shift, and interpretation, the three nested graphs match after the environment is updated at each binder, and the conditional and successor clauses agree.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem dollarStepTerm_interp :
    interp dollarStepTerm (fun _ => botElem) = graph termDollarStep := by
  unfold dollarStepTerm termDollarStep termDollarStepBody termShift interp
  apply congrArg graph
  funext s
  simp only [envSet]
  apply congrArg graph
  funext u
  simp only [envSet]
  apply congrArg graph
  funext z
  simp [envSet, condSet, succSet]
  rfl

end DomainTheory.DataTypesAsLattices
