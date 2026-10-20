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
