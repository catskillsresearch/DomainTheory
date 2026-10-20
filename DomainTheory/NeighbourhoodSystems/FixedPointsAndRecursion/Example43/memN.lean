module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Example43

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

/-- Membership in Scott's natural-number system: a neighbourhood is the whole space `ℕ` or a
singleton `{n}`. -/
def memN (X : Set ℕ) : Prop := X = Set.univ ∨ ∃ n, X = {n}

end DomainTheory.NeighbourhoodSystems.Example43
