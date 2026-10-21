/-ai
Flip complements every bit of a finite string by mapping Boolean negation along the string.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise516

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

/-- Complement every bit of a finite string. -/
abbrev flip (σ : Str) : Str := σ.map not

end DomainTheory.NeighbourhoodSystems.Exercise516
