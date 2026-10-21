/-ai
The lazy-naturals expression sends a domain X to the separated sum of the one-point domain with X, the right-hand side of M congruent to {{Λ}} + M.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise622.Cone

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

namespace Exercise619

/-- `T(X) = {{Λ}} + X` — the right-hand side of `M ≅ {{Λ}} + M`. -/
def MExpr : GExpr := .sum (.const Cone) .var

end Exercise619

end DomainTheory.NeighbourhoodSystems
