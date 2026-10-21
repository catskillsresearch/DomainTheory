/-ai
The environment retract is the graph of the map sending t to the graph of the map sending n to the application of the lambda retract to the application of t at n. Scott's formula (4.40) is λt. lamb ∘ seq(t).
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst36
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst55
public import DomainTheory.DataTypesAsLattices.Retracts.lambR

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (4.40).** `env = λt. lamb ∘ seq(t)`. -/
def envR : Pomega :=
  graph (fun t => graph (fun n => funOf lambR (funOf t n)))

end DomainTheory.DataTypesAsLattices
