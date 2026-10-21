/-ai
The first projection sends the sharp pairing of elements x and y to x.

A neighbourhood of the pair is either the master neighbourhood or a pair of a neighbourhood of x with a neighbourhood of y. In the master case the relation forces the codomain to be the master neighbourhood, which belongs to x, because a pair embedding is distinct from the master neighbourhood. In the pair case, either the codomain is again the master neighbourhood, or the two pair decompositions agree and the inclusion of the left component places the codomain above a neighbourhood of x. Conversely, if Z belongs to x, the pair embedding of Z with the master neighbourhood belongs to the sharp pair, since the master neighbourhood belongs to y, and the relation holds with left component Z.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Combinators77.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)


/-- **`proj0Map` really is the first projection of the pair part:** `proj₀(⟨x, y⟩^§) = x`. -/
theorem proj0_toElementMap_pairSharp (x y : (Dsharp D hD).Element) :
    (proj0Map hD).toElementMap (pairSharp D hD x y) = x := by
  apply Element.ext
  intro Z
  simp only [ApproximableMap.mem_toElementMap, proj0Map_rel]
  constructor
  · rintro ⟨W, hWmem, hMW, hMZ, hdisj⟩
    rcases hWmem with rfl | ⟨Pp, Qq, hxP, hyQ, rfl⟩
    · rcases hdisj with rfl | ⟨Pp', Qq', hPe, -⟩
      · exact x.master_mem
      · exact absurd hPe.symm (embPair_ne_Gamma D hD Pp' Qq')
    · rcases hdisj with rfl | ⟨Pp', Qq', hPe, hP'Z⟩
      · exact x.master_mem
      · obtain ⟨hPP, -⟩ := embPair_injective hPe
        exact x.up_mem hxP hMZ (by rw [hPP]; exact hP'Z)
  · intro hxZ
    exact ⟨embPair Z (Gamma D), Or.inr ⟨Z, Gamma D, hxZ, y.master_mem, rfl⟩,
      MemS.pair (x.sub hxZ) MemS.gamma, x.sub hxZ, Or.inr ⟨Z, Gamma D, rfl, subset_rfl⟩⟩

end Proposition77
end DomainTheory.NeighbourhoodSystems
