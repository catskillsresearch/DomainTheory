/-ai
An approximable self-map is a finitary projection when it is a projection and it is finitary.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition82
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83.IsProjection
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83.IsFinitary

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {D E : NeighborhoodSystem α}

/-- A **finitary projection**: both clauses of Definition 8.3 together with `IsRetraction`. -/
def IsFinitaryProjection (a : ApproximableMap E E) : Prop := IsProjection a ∧ IsFinitary a

end DomainTheory.NeighbourhoodSystems
