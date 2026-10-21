/-ai
The second projection sends the sharp pairing of two elements to the second element.

A neighbourhood of the image comes from a neighbourhood of the pairing. The master neighbourhood forces the target to be the master of the second element, since a paired embedding is not the master. A paired neighbourhood either again yields the master or, by injectivity of the paired embedding, has right-hand child taken from the second element, and upward closure applies. Conversely, a neighbourhood of the second element is reached from the paired embedding of the master neighbourhood with that neighbourhood.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Combinators77
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)




/-- **`proj1Map` really is the second projection of the pair part:** `proj₁(⟨x, y⟩^§) = y`. -/
theorem proj1_toElementMap_pairSharp (x y : (Dsharp D hD).Element) :
    (proj1Map hD).toElementMap (pairSharp D hD x y) = y := by
  apply Element.ext
  intro Z
  simp only [ApproximableMap.mem_toElementMap, proj1Map_rel]
  constructor
  · rintro ⟨W, hWmem, hMW, hMZ, hdisj⟩
    rcases hWmem with rfl | ⟨Pp, Qq, hxP, hyQ, rfl⟩
    · rcases hdisj with rfl | ⟨Pp', Qq', hPe, -⟩
      · exact y.master_mem
      · exact absurd hPe.symm (embPair_ne_Gamma D hD Pp' Qq')
    · rcases hdisj with rfl | ⟨Pp', Qq', hPe, hQ'Z⟩
      · exact y.master_mem
      · obtain ⟨-, hQQ⟩ := embPair_injective hPe
        exact y.up_mem hyQ hMZ (by rw [hQQ]; exact hQ'Z)
  · intro hyZ
    exact ⟨embPair (Gamma D) Z, Or.inr ⟨Gamma D, Z, x.master_mem, hyZ, rfl⟩,
      MemS.pair MemS.gamma (y.sub hyZ), y.sub hyZ, Or.inr ⟨Gamma D, Z, rfl, subset_rfl⟩⟩

end Proposition77
end DomainTheory.NeighbourhoodSystems
