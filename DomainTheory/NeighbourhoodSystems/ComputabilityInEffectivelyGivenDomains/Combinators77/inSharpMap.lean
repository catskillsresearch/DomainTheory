/-ai
Scott's injection from a neighbourhood system D to its sharp system, as an approximable map, relates a neighbourhood X to a sharp neighbourhood W when the zero-embedding of X is contained in W. The master neighbourhood is related to the master neighbourhood of the sharp system, because the zero-embedding of the master neighbourhood is contained there. The intersection of two related codomain neighbourhoods still contains the zero-embedding and remains a sharp neighbourhood. If the domain neighbourhood is replaced by a smaller one and the codomain neighbourhood by a larger one, monotonicity of the zero-embedding preserves the inclusion.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Combinators77.dsharpPresentation_X

@[expose] public section

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
