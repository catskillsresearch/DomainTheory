module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.interStepTerm

@[expose] public section

set_option linter.unusedSectionVars false

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

theorem interStepTerm_interp :
    interp interStepTerm (fun _ => botElem) = graph interStep := by
  unfold interStepTerm interStep
  simp only [interp, envSet, Function.update_self]
  apply congrArg graph
  funext f
  apply congrArg graph
  funext x
  apply congrArg graph
  funext y
  congr 2
  exact eq_2_14

end DomainTheory.DataTypesAsLattices
