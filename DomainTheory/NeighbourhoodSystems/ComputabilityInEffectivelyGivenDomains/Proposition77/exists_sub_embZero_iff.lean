module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp_odd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.memS_sub_embZero

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

theorem exists_sub_embZero_iff (hD : ∀ X, D.mem X → X.Nonempty) (Y : Set α) :
    (∃ l, Vsharp D P l ⊆ embZero Y) ↔ ∃ k, P.X k ⊆ Y := by
  constructor
  · rintro ⟨l, hl⟩
    obtain ⟨Z, hZ, hWZ⟩ := memS_sub_embZero hD (Vsharp_mem P l) hl
    rw [hWZ] at hl
    obtain ⟨k, hk⟩ := P.surj hZ
    exact ⟨k, hk ▸ embZero_subset.mp hl⟩
  · rintro ⟨k, hk⟩
    exact ⟨2 * k + 1, by rw [Vsharp_odd]; exact embZero_subset.mpr hk⟩

end Proposition77

end DomainTheory.NeighbourhoodSystems
