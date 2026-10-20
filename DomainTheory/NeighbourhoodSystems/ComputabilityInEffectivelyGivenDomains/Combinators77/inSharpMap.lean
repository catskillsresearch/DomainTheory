/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Combinators77.dsharpPresentation_X

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)

/-- **Example 6.1's injection `λx. x^§` as an approximable map.** Scott's neighbourhood relation
`X (λx.x^§) W ↔ 0·X ⊆ W` (`embZero X ⊆ W`). The filter laws are immediate: `inter_right` uses
`memS_inter` (with witness `0·X`), and `mono` uses monotonicity of `embZero`. -/
def inSharpMap : ApproximableMap D (Dsharp D hD) where
  rel X W := D.mem X ∧ MemS D W ∧ embZero X ⊆ W
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨D.master_mem, MemS.gamma, embZero_subset_Gamma D.master_mem⟩
  inter_right := by
    rintro X W W' ⟨hX, hW, hsub⟩ ⟨-, hW', hsub'⟩
    exact ⟨hX, memS_inter hD hW hW' (MemS.zero hX) (Set.subset_inter hsub hsub'),
      Set.subset_inter hsub hsub'⟩
  mono := by
    rintro X X' W W' ⟨hX, hW, hsub⟩ hX'X hWW' hX'mem hW'mem
    exact ⟨hX'mem, hW'mem, (embZero_subset.mpr hX'X).trans (hsub.trans hWW')⟩

end Proposition77

end DomainTheory.NeighbourhoodSystems
