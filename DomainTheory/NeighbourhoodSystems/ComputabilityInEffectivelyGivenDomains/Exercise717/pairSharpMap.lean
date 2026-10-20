module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Combinators77
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717.proj1Map_rel

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)

/-- **Example 6.1's pairing constructor `pair : D^§ × D^§ → D^§`, as a joint approximable map.**
`(A ∪ B) pair W ↔ A, B ∈ 𝒟^§ ∧ W ∈ 𝒟^§ ∧ 1·A ∪ 2·B ⊆ W` (with `A ∪ B = prodNbhd A B`). -/
def pairSharpMap : ApproximableMap (prod (Dsharp D hD) (Dsharp D hD)) (Dsharp D hD) where
  rel V W := (prod (Dsharp D hD) (Dsharp D hD)).mem V ∧ MemS D W ∧
    ∃ A B, MemS D A ∧ MemS D B ∧ V = prodNbhd A B ∧ embPair A B ⊆ W
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(prod (Dsharp D hD) (Dsharp D hD)).master_mem, MemS.gamma,
    ⟨Gamma D, Gamma D, MemS.gamma, MemS.gamma, rfl, embPair_subset_Gamma subset_rfl subset_rfl⟩⟩
  inter_right := by
    rintro V W W' ⟨hV, hW, A, B, hA, hB, rfl, hsub⟩ ⟨-, hW', A', B', hA', hB', heq, hsub'⟩
    obtain ⟨rfl, rfl⟩ := prodNbhd_injective heq
    exact ⟨hV, memS_inter hD hW hW' (MemS.pair hA hB) (Set.subset_inter hsub hsub'),
      A, B, hA, hB, rfl, Set.subset_inter hsub hsub'⟩
  mono := by
    rintro V V' W W' ⟨hV, hW, A, B, hA, hB, rfl, hsub⟩ hV'V hWW' hV'mem hW'mem
    obtain ⟨A', B', hA', hB', rfl⟩ := hV'mem
    obtain ⟨hA'A, hB'B⟩ := prodNbhd_subset_iff.mp hV'V
    exact ⟨prod_mem_prodNbhd hA' hB', hW'mem, A', B', hA', hB', rfl,
      (embPair_subset.mpr ⟨hA'A, hB'B⟩).trans (hsub.trans hWW')⟩

end Proposition77

end DomainTheory.NeighbourhoodSystems
