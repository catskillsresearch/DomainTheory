/-ai
Equal left copies come from equal underlying sets.

Each inclusion of left copies is equivalent to the corresponding inclusion of sets, so the two inclusions obtained from an equality of copies give equality of the sets.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Insert
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}


theorem inj₀_injective {X X' : Set α} (h : (inj₀ X : Set (Option (α ⊕ β))) = inj₀ X') : X = X' :=
  Set.Subset.antisymm (inj₀_subset_inj₀.mp h.subset) (inj₀_subset_inj₀.mp h.symm.subset)

end DomainTheory.NeighbourhoodSystems
