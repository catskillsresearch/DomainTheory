module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62








variable {α β γ : Type*}

























theorem j0_injective {X X' : Set α}
    (h : (j0 X : Set (Option (α ⊕ β ⊕ γ))) = j0 X') : X = X' :=
  Set.Subset.antisymm (j0_subset_j0.mp h.subset) (j0_subset_j0.mp h.symm.subset)

end DomainTheory.NeighbourhoodSystems
