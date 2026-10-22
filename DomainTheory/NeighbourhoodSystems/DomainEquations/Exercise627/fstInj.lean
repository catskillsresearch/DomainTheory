module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}

/-- The injection `i : 𝒟 → 𝒟 × ℰ`: `X i W ↔ X ∈ 𝒟 ∧ W ∈ 𝒟×ℰ ∧ (X,Δ₁) ⊆ W`. -/
def fstInj (D₀ D₁ : NeighborhoodSystem Str) : ApproximableMap D₀ (prodTok D₀ D₁) where
  rel X W := D₀.mem X ∧ (prodTok D₀ D₁).mem W ∧ prodTokNbhd X D₁.master ⊆ W
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨D₀.master_mem, (prodTok D₀ D₁).master_mem, subset_rfl⟩
  inter_right := by
    rintro X W W' ⟨hX, hW, hsub⟩ ⟨_, hW', hsub'⟩
    exact ⟨hX, (prodTok D₀ D₁).inter_mem hW hW' (prodTok_mem_prodTokNbhd hX D₁.master_mem)
      (Set.subset_inter hsub hsub'), Set.subset_inter hsub hsub'⟩
  mono := by
    rintro X X' W W' ⟨_, _, hsub⟩ hX'X hWW' hX' hW'
    exact ⟨hX', hW', ((prodTokNbhd_subset_iff.mpr ⟨hX'X, subset_rfl⟩).trans hsub).trans hWW'⟩

end Exercise627

end DomainTheory.NeighbourhoodSystems
