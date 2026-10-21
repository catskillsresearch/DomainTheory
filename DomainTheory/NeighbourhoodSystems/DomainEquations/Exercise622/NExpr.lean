/-ai
The vertical-naturals expression sends a domain X to the coalesced sum of the two-point domain with X, the right-hand side of N congruent to {{0}, {0, Λ}} ⊕ N.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise622.Cnat

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

namespace Exercise619

/-- `T(X) = {{0},{0,Λ}} ⊕ X` — the right-hand side of `N ≅ {{0},{0,Λ}} ⊕ N`. -/
def NExpr : GExpr := .oplus (.const Cnat) .var

end Exercise619

end DomainTheory.NeighbourhoodSystems
