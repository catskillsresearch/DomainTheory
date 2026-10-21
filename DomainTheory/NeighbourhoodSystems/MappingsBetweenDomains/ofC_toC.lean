/-ai
Applying ofC to the set represented by an ideal element recovers that element.

Compare membership of a neighbourhood. If it belongs to ofC of the represented set, some token contained in that set has its neighbourhood contained in the given neighbourhood. The membership identity puts that token neighbourhood in the element, and upward closure puts the given neighbourhood in the element. Conversely, a neighbourhood of the element is the neighbourhood of some token, and that token is contained in the represented set, so it witnesses membership.
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

set_option linter.unusedSectionVars false

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
