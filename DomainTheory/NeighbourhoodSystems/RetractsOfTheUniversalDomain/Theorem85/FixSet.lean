/-ai
FixSet a is the fixed-point set of an approximable endomap a, the subtype of elements sent to themselves, matching the witness type of a finitary map.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

/-- The fixed-point set of `a`, as a bare type — matching `IsFinitary`'s witness type. -/
abbrev FixSet (a : ApproximableMap E E) := {y : E.Element // a.toElementMap y = y}

end DomainTheory.NeighbourhoodSystems
