module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.memC_singleton
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.C
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.C_mem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.C_master

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example44

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB

/-- Scott's total element `σ = ↑{σ}` (the finite sequence `σ`, completed). -/
def strElem (σ : Str) : C.Element := C.principal (C_mem.mpr (memC_singleton σ))

end DomainTheory.NeighbourhoodSystems.Example44
