module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.whichGuard

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

theorem whichGuard_left {W : Set (Option (α ⊕ β))} {C : Set Example12.Token} {X : Set α}
    (hg : whichGuard V₀ V₁ W C) (hW : W = inj₀ X) (hX : X.Nonempty) :
    C = Example12.master ∨ C = Example12.zero := by
  rcases hg with ⟨_, hc⟩ | ⟨⟨Y, _, hWY⟩, _⟩ | ⟨hWsm, _⟩
  · exact hc
  · refine absurd (hW.symm.trans hWY) ?_
    intro h; exact not_inj₀_subset_inj₁ hX h.subset
  · refine absurd (hW.symm.trans hWsm) ?_
    intro h; exact none_mem_inj₀ (h ▸ none_mem_sumMaster)

end DomainTheory.NeighbourhoodSystems.Exercise326
