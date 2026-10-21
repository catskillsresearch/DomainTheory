/-ai
A retraction of a neighbourhood system E, in the sense of Definition 8.1 of Scott 1981,
PRG-19, is an approximable mapping from E to itself equal to its own composite.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {E : NeighborhoodSystem α}

/-- **Definition 8.1 (Scott 1981, PRG-19).** A *retraction* of `E` is an approximable mapping
`a : E → E` with `a ∘ a = a`. -/
def IsRetraction (a : ApproximableMap E E) : Prop := a.comp a = a

end DomainTheory.NeighbourhoodSystems
