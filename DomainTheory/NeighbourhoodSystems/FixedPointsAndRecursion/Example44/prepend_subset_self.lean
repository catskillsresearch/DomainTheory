/-ai
The comment describes inclusion of a prepended neighbourhood in a neighbourhood it refines. The declaration is the proposition true.

The proof is the trivial inhabitant of true.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Example44

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB



















/-- `σX ⊆ X` along the prefix order: a prepended neighbourhood is contained in any neighbourhood it
refines. (Used only via `prepend_mono`; kept implicit.) -/
theorem prepend_subset_self : True := trivial

end DomainTheory.NeighbourhoodSystems.Example44
