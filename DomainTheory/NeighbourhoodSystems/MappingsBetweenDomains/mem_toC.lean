/-ai
An element belongs to the set represented by an ideal element if and only if it belongs to the closure of some token whose neighbourhood belongs to the ideal element.

Unfold the represented set as the union of the associated family. A member of that union lies in some set of the family, which is the closure of such a token. Conversely, that closure itself belongs to the family.
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
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Tok
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.nbhd
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.mem_nbhd
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.reprSystem
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.mem_reprSystem
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.reprSystem_master
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.famC
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.toC

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise222

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {τ : Type*} (C : Set (Set τ))

variable (hInter : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → ⋂₀ 𝒮 ∈ C)

variable (hne : C.Nonempty)

theorem mem_toC (x : (reprSystem C hInter hne).Element) {t : τ} :
    t ∈ toC C hInter hne x ↔ ∃ F : Tok C, x.mem (nbhd C F.1) ∧ t ∈ Cl C F.1 := by
  simp only [toC, famC, Set.mem_sUnion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨Y, ⟨F, hF, rfl⟩, ht⟩
    exact ⟨F, hF, ht⟩
  · rintro ⟨F, hF, ht⟩
    exact ⟨Cl C F.1, ⟨F, hF, rfl⟩, ht⟩

end DomainTheory.NeighbourhoodSystems.Exercise222
