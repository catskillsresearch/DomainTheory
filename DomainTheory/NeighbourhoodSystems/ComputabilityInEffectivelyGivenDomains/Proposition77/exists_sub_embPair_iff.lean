module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp_surj
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.memS_sub_embPair

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

theorem exists_sub_embPair_iff (hD : ∀ X, D.mem X → X.Nonempty)
    (A B : Set (List Bool × α)) :
    (∃ l, Vsharp D P l ⊆ embPair A B) ↔
      (∃ l, Vsharp D P l ⊆ A) ∧ (∃ l, Vsharp D P l ⊆ B) := by
  constructor
  · rintro ⟨l, hl⟩
    obtain ⟨Pp, Qq, hP, hQ, hWeq⟩ := memS_sub_embPair hD (Vsharp_mem P l) hl
    rw [hWeq] at hl
    obtain ⟨hPA, hQB⟩ := embPair_subset.mp hl
    obtain ⟨l1, h1⟩ := Vsharp_surj P hP
    obtain ⟨l2, h2⟩ := Vsharp_surj P hQ
    exact ⟨⟨l1, h1 ▸ hPA⟩, ⟨l2, h2 ▸ hQB⟩⟩
  · rintro ⟨⟨l1, h1⟩, ⟨l2, h2⟩⟩
    obtain ⟨l, hl⟩ := Vsharp_surj P (MemS.pair (Vsharp_mem P l1) (Vsharp_mem P l2))
    exact ⟨l, by rw [hl]; exact embPair_subset.mpr ⟨h1, h2⟩⟩

end Proposition77

end DomainTheory.NeighbourhoodSystems
