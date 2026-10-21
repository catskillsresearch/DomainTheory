/-ai
A set of strings is a neighbourhood of the binary-sequence system if and only if it satisfies the binary-sequence neighbourhood predicate.

The two sides agree by reflexivity of equivalence.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.memC
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.C

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Example44

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB

@[simp] theorem C_mem {X : Set Str} : C.mem X ↔ memC X := Iff.rfl

end DomainTheory.NeighbourhoodSystems.Example44
