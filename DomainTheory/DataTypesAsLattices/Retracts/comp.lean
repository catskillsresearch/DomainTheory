/-ai
Composition of u after v is the graph of the map sending x to the application of u to the application of v to x. Scott's formula (4.5) is u ∘ v = λx. u(v(x)).
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (4.5).** Composition `u ∘ v = λx. u(v(x))`. -/
def comp (u v : Pomega) : Pomega :=
  graph (fun x => funOf u (funOf v x))

end DomainTheory.DataTypesAsLattices
