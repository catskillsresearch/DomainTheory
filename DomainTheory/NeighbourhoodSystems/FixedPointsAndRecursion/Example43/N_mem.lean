/-ai
A set is a neighbourhood of the natural-number system if and only if it satisfies the natural-number neighbourhood predicate.

The two sides agree by reflexivity of equivalence.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.memN
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.N

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Example43

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

@[simp] theorem N_mem {X : Set ℕ} : N.mem X ↔ memN X := Iff.rfl

end DomainTheory.NeighbourhoodSystems.Example43
