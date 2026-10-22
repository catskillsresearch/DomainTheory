module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
public import Mathlib.Order.Directed

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise222

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {τ : Type*} (C : Set (Set τ))

/-- The **closure** `F̄ = ⋂ {X ∈ C ∣ F ⊆ X}` of a set `F` relative to the family `C`. -/
def Cl (F : Set τ) : Set τ := ⋂₀ {X | X ∈ C ∧ F ⊆ X}

end DomainTheory.NeighbourhoodSystems.Exercise222
