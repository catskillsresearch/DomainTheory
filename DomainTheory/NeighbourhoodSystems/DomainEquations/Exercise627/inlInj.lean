/-ai
The left injection of D₀ into the coalesced sum relates X to W when X is a neighbourhood of D₀, W is a coalesced-sum neighbourhood, and the left copy of X is contained in W. The masters are related because the left copy of the master is contained in the coalesced-sum master. An intersection on the right uses the coalesced-sum intersection law at the neighbourhood given by the left copy of X, and the two inclusions combine. If X' lies below X, the left copy of X' is contained in the left copy of X, so the inclusions compose.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.leftN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.leftN_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.leftN_subset_iff
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.oplus_mem_leftN

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

/-- The injection `i : 𝒟 → 𝒟 ⊕ ℰ`: `X i W ↔ X ∈ 𝒟 ∧ W ∈ 𝒟⊕ℰ ∧ leftN X ⊆ W`. -/
def inlInj : ApproximableMap D₀ (oplusTok D₀ D₁ h₀ h₁) where
  rel X W := D₀.mem X ∧ (oplusTok D₀ D₁ h₀ h₁).mem W ∧ leftN D₀ D₁ X ⊆ W
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨D₀.master_mem, (oplusTok D₀ D₁ h₀ h₁).master_mem, leftN_master.le⟩
  inter_right := by
    rintro X W W' ⟨hX, hW, hsub⟩ ⟨_, hW', hsub'⟩
    exact ⟨hX, (oplusTok D₀ D₁ h₀ h₁).inter_mem hW hW' (oplus_mem_leftN hX)
      (Set.subset_inter hsub hsub'), Set.subset_inter hsub hsub'⟩
  mono := by
    rintro X X' W W' ⟨hX, _, hsub⟩ hX'X hWW' hX' hW'
    exact ⟨hX', hW', ((leftN_subset_iff hX' hX).mpr hX'X).trans (hsub.trans hWW')⟩

end Exercise627

end DomainTheory.NeighbourhoodSystems
