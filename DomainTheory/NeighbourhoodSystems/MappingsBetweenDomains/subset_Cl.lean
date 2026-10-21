/-ai
Every set is contained in its closure relative to the family.

An element of the set belongs to every member of the family that contains the set, which is membership in the intersection defining the closure.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Lattice.Bounded
import all Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
import all Mathlib.Data.Set.Lattice.Disjoint
public import Mathlib.Order.Directed
import all Mathlib.Order.Directed
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Cl

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise222

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {τ : Type*} (C : Set (Set τ))

/-- `F ⊆ F̄`: a set is contained in its closure. -/
theorem subset_Cl (F : Set τ) : F ⊆ Cl C F := by
  intro t ht
  rw [Cl, Set.mem_sInter]
  intro X hX
  exact hX.2 ht

end DomainTheory.NeighbourhoodSystems.Exercise222
