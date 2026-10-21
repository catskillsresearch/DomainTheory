/-ai
The neighbourhood of the empty token belongs to every ideal element of the representation system.

The underlying set of the empty token is empty, the neighbourhood of the empty set is the set of all tokens, and every element contains the master neighbourhood.
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
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.nbhd_empty
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.botTok
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.reprSystem
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.mem_reprSystem
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.reprSystem_master

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise222

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {τ : Type*} (C : Set (Set τ))

variable (hInter : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → ⋂₀ 𝒮 ∈ C)

variable (hne : C.Nonempty)

/-- The empty token's neighbourhood `C(∅) = Δ` is in every element (it is the master). -/
theorem mem_nbhd_bot (x : (reprSystem C hInter hne).Element) :
    x.mem (nbhd C (botTok C hne).1) := by
  have h : (botTok C hne).1 = (∅ : Set τ) := rfl
  rw [h, nbhd_empty C]
  exact x.master_mem

end DomainTheory.NeighbourhoodSystems.Exercise222
