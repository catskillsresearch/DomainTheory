/-ai
If the neighbourhoods of two tokens both belong to an ideal element of the representation system, then some token has its neighbourhood in that element and the closures of the two tokens are both contained in its closure.

The intersection of the two neighbourhoods belongs to the element, so it is a neighbourhood of the representation system and equals the neighbourhood of some token. That token lies in its own neighbourhood, hence in the intersection, so each of the original tokens is contained in its closure. Since that closure belongs to the family, the closure operation preserves the two inclusions.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
public import Mathlib.Order.Directed
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Cl
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.subset_Cl
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Cl_subset
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Tok
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Cl_mem
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.nbhd
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.mem_nbhd
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.reprSystem
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.mem_reprSystem
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.reprSystem_master

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise222

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {τ : Type*} (C : Set (Set τ))

variable (hInter : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → ⋂₀ 𝒮 ∈ C)

variable (hne : C.Nonempty)

/-- **Directedness step.** If `C(F), C(F') ∈ x` then there is a token `F₃` with `C(F₃) ∈ x` whose
closure dominates both `F̄` and `F̄'`. (From the filter intersection `C(F) ∩ C(F') ∈ x`, which is
some `C(F₃)`.) -/
theorem directed_step (x : (reprSystem C hInter hne).Element) {F F' : Tok C}
    (hF : x.mem (nbhd C F.1)) (hF' : x.mem (nbhd C F'.1)) :
    ∃ F₃ : Tok C, x.mem (nbhd C F₃.1) ∧ Cl C F.1 ⊆ Cl C F₃.1 ∧ Cl C F'.1 ⊆ Cl C F₃.1 := by
  have hinter : x.mem (nbhd C F.1 ∩ nbhd C F'.1) := x.inter_mem hF hF'
  have hmemD : (reprSystem C hInter hne).mem (nbhd C F.1 ∩ nbhd C F'.1) := x.sub hinter
  obtain ⟨F₃, hF₃eq⟩ := hmemD
  rw [hF₃eq] at hinter
  have hF₃self : (F₃ : Tok C) ∈ nbhd C F₃.1 := subset_Cl C F₃.1
  rw [← hF₃eq] at hF₃self
  refine ⟨F₃, hinter, ?_, ?_⟩
  · exact Cl_subset C (Cl_mem C hInter F₃.2.2) hF₃self.1
  · exact Cl_subset C (Cl_mem C hInter F₃.2.2) hF₃self.2

end DomainTheory.NeighbourhoodSystems.Exercise222
