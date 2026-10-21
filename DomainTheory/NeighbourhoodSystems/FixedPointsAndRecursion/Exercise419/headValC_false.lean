/-ai
The head value of a binary string beginning with false is the false-bit constant.

The equation is the corresponding clause of the head-value definition.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.headValC
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.headValC_nil

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise419

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44

variable {β : Type*}

@[simp] theorem headValC_false (V : NeighborhoodSystem β) (z a0 a1 : V.Element) (σ : Str) :
    headValC V z a0 a1 (false :: σ) = a0 := rfl

end DomainTheory.NeighbourhoodSystems.Exercise419
