module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
public import Mathlib.Order.Directed
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.mem_nbhd
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.reprSystem
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.mem_reprSystem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise222

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {τ : Type*} (C : Set (Set τ))

variable (hInter : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → ⋂₀ 𝒮 ∈ C)

variable (hne : C.Nonempty)

@[simp] theorem reprSystem_master : (reprSystem C hInter hne).master = Set.univ := rfl

end DomainTheory.NeighbourhoodSystems.Exercise222
