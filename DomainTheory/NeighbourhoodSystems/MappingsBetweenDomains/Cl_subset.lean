/-ai
The closure of F is contained in every member of the family that contains F.

A point of the closure lies in every such member, and the given member is one of them.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
public import Mathlib.Order.Directed
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Cl

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise222

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {τ : Type*} (C : Set (Set τ))

/-- `F̄ ⊆ X` whenever `X ∈ C` contains `F`: the closure is the *smallest* member of `C` over `F`. -/
theorem Cl_subset {F X : Set τ} (hX : X ∈ C) (hFX : F ⊆ X) : Cl C F ⊆ X := by
  intro t ht
  exact (Set.mem_sInter.mp ht) X ⟨hX, hFX⟩

end DomainTheory.NeighbourhoodSystems.Exercise222
