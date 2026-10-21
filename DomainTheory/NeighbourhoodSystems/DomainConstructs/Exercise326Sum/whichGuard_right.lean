/-ai
If the guard holds and the sum neighborhood is a right injection of a nonempty set, then the truth neighborhood is the master or one.

Splitting the guard, the right clause is the claim. A left injection cannot equal that right injection, because a nonempty right copy is not contained in a left copy. The sum master cannot equal it either, because the master contains the empty token and a right injection does not.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.whichGuard

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

theorem whichGuard_right {W : Set (Option (α ⊕ β))} {C : Set Example12.Token} {Y : Set β}
    (hg : whichGuard V₀ V₁ W C) (hW : W = inj₁ Y) (hY : Y.Nonempty) :
    C = Example12.master ∨ C = Example12.one := by
  rcases hg with ⟨⟨X, _, hWX⟩, _⟩ | ⟨_, hc⟩ | ⟨hWsm, _⟩
  · refine absurd (hW.symm.trans hWX) ?_
    intro h; exact not_inj₁_subset_inj₀ hY h.subset
  · exact hc
  · refine absurd (hW.symm.trans hWsm) ?_
    intro h; exact none_mem_inj₁ (h ▸ none_mem_sumMaster)

end DomainTheory.NeighbourhoodSystems.Exercise326
