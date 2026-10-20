/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Proposition77
public import DomainTheory.Neighborhood.Combinators77.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

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
end DomainTheory.Neighborhood
