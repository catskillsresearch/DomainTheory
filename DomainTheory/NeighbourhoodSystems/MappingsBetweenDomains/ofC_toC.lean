module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
public import Mathlib.Order.Directed
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.nbhd
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.mem_nbhd
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.reprSystem
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.mem_reprSystem
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.reprSystem_master
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.toC
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.mem_nbhd_iff
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ofC
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.toC_mem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise222

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {τ : Type*} (C : Set (Set τ))

variable (hInter : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → ⋂₀ 𝒮 ∈ C)

variable (hne : C.Nonempty)

variable (hDir : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → DirectedOn (· ⊆ ·) 𝒮 → ⋃₀ 𝒮 ∈ C)

/-- The other round-trip `ofC (toC x) = x`. -/
theorem ofC_toC (x : (reprSystem C hInter hne).Element) :
    ofC C hInter hne (toC C hInter hne x) (toC_mem C hInter hne hDir x) = x := by
  apply Element.ext
  intro N
  constructor
  · rintro ⟨hN, F, hFtoC, hFN⟩
    have hxF : x.mem (nbhd C F.1) := (mem_nbhd_iff C hInter hne x F).mpr hFtoC
    exact x.up_mem hxF hN hFN
  · intro hxN
    have hN : (reprSystem C hInter hne).mem N := x.sub hxN
    obtain ⟨G, rfl⟩ := hN
    have hGtoC : G.1 ⊆ toC C hInter hne x := (mem_nbhd_iff C hInter hne x G).mp hxN
    exact ⟨⟨G, rfl⟩, G, hGtoC, subset_rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise222
