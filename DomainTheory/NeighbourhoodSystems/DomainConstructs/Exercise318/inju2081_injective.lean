module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Insert
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}


theorem inj₁_injective {Y Y' : Set β} (h : (inj₁ Y : Set (Option (α ⊕ β))) = inj₁ Y') : Y = Y' :=
  Set.Subset.antisymm (inj₁_subset_inj₁.mp h.subset) (inj₁_subset_inj₁.mp h.symm.subset)

end DomainTheory.NeighbourhoodSystems
