/-ai
Strn A is the type of finite A-strings, identified with the type of lists of elements of A.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise617Gen

set_option linter.unusedSectionVars false

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

variable {A : Type} [DecidableEq A]

/-- The token type `A*` of finite `A`-strings. -/
abbrev Strn (A : Type) := List A

end DomainTheory.NeighbourhoodSystems.Exercise617Gen
