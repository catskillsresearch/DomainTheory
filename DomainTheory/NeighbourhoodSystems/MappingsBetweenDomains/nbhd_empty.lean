module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
public import Mathlib.Order.Directed
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.nbhd
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.mem_nbhd

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise222

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {τ : Type*} (C : Set (Set τ))

variable (hInter : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → ⋂₀ 𝒮 ∈ C)

/-- `C(∅) = Δ`: the empty token's neighbourhood is everything (the master). -/
theorem nbhd_empty : nbhd C (∅ : Set τ) = Set.univ := by
  ext G
  simp [nbhd]

end DomainTheory.NeighbourhoodSystems.Exercise222
