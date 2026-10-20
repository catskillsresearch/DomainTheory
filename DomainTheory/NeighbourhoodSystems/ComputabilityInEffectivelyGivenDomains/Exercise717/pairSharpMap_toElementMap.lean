/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Combinators77
public import DomainTheory.Neighborhood.Theorem74
public import DomainTheory.Neighborhood.Exercise717.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)







/-- **`pairSharpMap` really is Example 6.1's pairing:** `pair(x, y) ↦ ⟨x, y⟩^§` (`pairSharp`). -/
theorem pairSharpMap_toElementMap (x y : (Dsharp D hD).Element) :
    (pairSharpMap hD).toElementMap (DomainTheory.Neighborhood.pair x y) = pairSharp D hD x y := by
  apply Element.ext
  intro W
  simp only [ApproximableMap.mem_toElementMap, pairSharpMap_rel, mem_pair]
  constructor
  · rintro ⟨V, ⟨A0, B0, hxA0, hyB0, rfl⟩, -, hW, A, B, -, -, heq, hsub⟩
    obtain ⟨rfl, rfl⟩ := prodNbhd_injective heq
    exact (pairSharp D hD x y).up_mem (Or.inr ⟨A0, B0, hxA0, hyB0, rfl⟩) hW hsub
  · intro hW
    rcases hW with rfl | ⟨P, Q, hxP, hyQ, rfl⟩
    · exact ⟨prodNbhd (Gamma D) (Gamma D), ⟨Gamma D, Gamma D, x.master_mem, y.master_mem, rfl⟩,
        ⟨Gamma D, Gamma D, MemS.gamma, MemS.gamma, rfl⟩, MemS.gamma,
        Gamma D, Gamma D, MemS.gamma, MemS.gamma, rfl,
        embPair_subset_Gamma subset_rfl subset_rfl⟩
    · exact ⟨prodNbhd P Q, ⟨P, Q, hxP, hyQ, rfl⟩, prod_mem_prodNbhd (x.sub hxP) (y.sub hyQ),
        MemS.pair (x.sub hxP) (y.sub hyQ), P, Q, x.sub hxP, y.sub hyQ, rfl, subset_rfl⟩

end Proposition77
end DomainTheory.Neighborhood
