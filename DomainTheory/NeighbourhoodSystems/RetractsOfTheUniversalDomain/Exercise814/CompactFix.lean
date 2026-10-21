/-ai
A compact fixed point of a closure operator is a fixed point that is compact with respect to directed unions taken in the fixed-point set.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.IsClosureOperator
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.IsCompactFix

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

section FiniteDomain

variable {a : ApproximableMap E E} (h : IsClosureOperator a)

/-- The compact ("finite") fixed points of `a`, as a subtype of `Fix(a)`. -/
def CompactFix (h : IsClosureOperator a) := {y : FixSet a // IsCompactFix h y}

end FiniteDomain

end DomainTheory.NeighbourhoodSystems
