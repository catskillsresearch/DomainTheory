/-ai
Scott's partial element determined by a finite string σ is the principal element of the neighbourhood system C on the cone of sequences that begin with σ.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.memC_cone
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.C
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.C_mem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.C_master

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example44

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB

/-- Scott's partial element `σ⊥ = ↑σΣ*` ("the sequence starts with `σ`"). -/
def strBot (σ : Str) : C.Element := C.principal (C_mem.mpr (memC_cone σ))

end DomainTheory.NeighbourhoodSystems.Example44
