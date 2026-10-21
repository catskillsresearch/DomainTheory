/-ai
If a family of sets is closed under nonempty intersections, and some member contains a set F, then the closure of F belongs to the family.

The closure is that intersection. The given member shows the family of members containing F is nonempty, every such member belongs to the family, and the intersection hypothesis applies.
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

variable (hInter : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → ⋂₀ 𝒮 ∈ C)

include hInter in
/-- Every closure `F̄` of a token lies in `C` (closure under non-empty intersection). -/
theorem Cl_mem {F : Set τ} (h : ∃ X ∈ C, F ⊆ X) : Cl C F ∈ C := by
  show ⋂₀ {X | X ∈ C ∧ F ⊆ X} ∈ C
  apply hInter
  · obtain ⟨X, hX, hFX⟩ := h
    exact ⟨X, hX, hFX⟩
  · intro X hX
    exact hX.1

end DomainTheory.NeighbourhoodSystems.Exercise222
