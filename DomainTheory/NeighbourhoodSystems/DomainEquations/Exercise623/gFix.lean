/-ai
The fixed-point token set of a grammar expression is the union of the Kleene iterates of its token function. The union is written explicitly, without a choice principle.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

/-- **The fixed-point token set `Γ = tok(T({Γ}))`**, as the explicit Kleene union `⋃ₙ gIter T n`
(no `Classical.choice`). -/
def gFix (T : GExpr) : Set Str := ⋃ n, gIter T n

end Exercise619

end DomainTheory.NeighbourhoodSystems
