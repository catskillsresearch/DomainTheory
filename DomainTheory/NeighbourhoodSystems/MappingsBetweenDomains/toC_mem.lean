module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
public import Mathlib.Order.Directed
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Cl
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Cl_mem
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.mem_nbhd
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.botTok
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.reprSystem
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.mem_reprSystem
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.reprSystem_master
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.famC
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.toC
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.directed_step
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.mem_nbhd_bot

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise222

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {τ : Type*} (C : Set (Set τ))

variable (hInter : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → ⋂₀ 𝒮 ∈ C)

variable (hne : C.Nonempty)

variable (hDir : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → DirectedOn (· ⊆ ·) 𝒮 → ⋃₀ 𝒮 ∈ C)

include hDir in
/-- `toC x ∈ C`: the represented set lies in the family (closure under directed unions). -/
theorem toC_mem (x : (reprSystem C hInter hne).Element) : toC C hInter hne x ∈ C := by
  show ⋃₀ famC C hInter hne x ∈ C
  apply hDir (famC C hInter hne x)
  · exact ⟨Cl C (botTok C hne).1, botTok C hne, mem_nbhd_bot C hInter hne x, rfl⟩
  · rintro Y ⟨F, _, rfl⟩
    exact Cl_mem C hInter F.2.out.2
  · rintro Y ⟨F, hF, rfl⟩ Y' ⟨F', hF', rfl⟩
    obtain ⟨F₃, hF₃, hFF₃, hF'F₃⟩ := directed_step C hInter hne x hF hF'
    exact ⟨Cl C F₃.1, ⟨F₃, hF₃, rfl⟩, hFF₃, hF'F₃⟩

end DomainTheory.NeighbourhoodSystems.Exercise222
