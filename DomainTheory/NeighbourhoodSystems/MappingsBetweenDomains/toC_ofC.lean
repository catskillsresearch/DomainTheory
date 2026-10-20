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
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.subset_Cl
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Cl_subset
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.IsTok
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.mem_nbhd
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.nbhd_subset_iff
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.mem_reprSystem
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.reprSystem_master
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.toC
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.mem_toC
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ofC

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise222

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {τ : Type*} (C : Set (Set τ))

variable (hInter : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → ⋂₀ 𝒮 ∈ C)

variable (hne : C.Nonempty)

/-- **Scott's identity** `X = ⋃ {F̄ ∣ F ⊆ X, F ∈ Δ}` in round-trip form: `toC (ofC X) = X`. -/
theorem toC_ofC (X : Set τ) (hX : X ∈ C) : toC C hInter hne (ofC C hInter hne X hX) = X := by
  apply Set.Subset.antisymm
  · intro t ht
    rw [mem_toC] at ht
    obtain ⟨F, hF, htCl⟩ := ht
    obtain ⟨_, F', hF'X, hF'F⟩ := hF
    have h1 : F.1 ⊆ Cl C F'.1 := (nbhd_subset_iff C hInter F'.2).mp hF'F
    have hFX : F.1 ⊆ X := h1.trans (Cl_subset C hX hF'X)
    exact Cl_subset C hX hFX htCl
  · intro t ht
    have hst : IsTok C {t} := ⟨Set.finite_singleton t, X, hX, Set.singleton_subset_iff.mpr ht⟩
    rw [mem_toC]
    refine ⟨⟨{t}, hst⟩, ?_, subset_Cl C {t} rfl⟩
    exact ⟨⟨⟨{t}, hst⟩, rfl⟩, ⟨{t}, hst⟩, Set.singleton_subset_iff.mpr ht, subset_rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise222
