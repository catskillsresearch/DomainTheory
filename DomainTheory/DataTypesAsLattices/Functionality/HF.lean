/-ai
Scott 1976, (4.45). The continuous operator HF at an interpreter H is the graph of the map sending an environment to the graph of one step of that interpreter in the term.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm
public import DomainTheory.DataTypesAsLattices.Functionality.Hstep

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (4.45).** Continuous operator whose least fixed point is
the syntax-directed interpreter. -/
def HF (H : Pomega) : Pomega :=
  graph (fun e => graph (fun t => Hstep H e t))

end DomainTheory.DataTypesAsLattices
