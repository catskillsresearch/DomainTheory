/-ai
The alternating element is the least fixed point of the composite that prepends true and then prepends false.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.C
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.C_mem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.C_master
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.consMap

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example44

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB

/-- **Example 4.4 — an element defined by a fixed-point equation.** Scott's `a = 01a`, the infinite
sequence that alternates `0`s and `1`s. We take the least fixed point of `x ↦ 0(1x)`
(`= consMap 0 ∘ consMap 1`), which exists by the Fixed-point Theorem 4.1. -/
def altElt : C.Element := ((consMap false).comp (consMap true)).fixElement

end DomainTheory.NeighbourhoodSystems.Example44
