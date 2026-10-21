/-ai
If the right injection of a set is a neighbourhood of the abstract sum, then that set is a neighbourhood of the second system.

The sum master contains the untagged token, which does not lie in a right injection, so the neighbourhood is not the master. A left injection of a nonempty neighbourhood contains a left-tagged token, which does not lie in a right injection. The remaining case is a right injection of a neighbourhood of the second system, and injectivity of the right injection identifies the set with that neighbourhood.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example62 ExampleB

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

theorem sum_mem_inj₁_inv {Y : Set Str} (h : (sum D₀ D₁ h₀ h₁).mem (inj₁ Y)) : D₁.mem Y := by
  rcases h with h0 | ⟨X', hX', heq⟩ | ⟨Y', hY', heq⟩
  · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₁
  · obtain ⟨a, ha⟩ := h₀ X' hX'
    exact absurd (heq ▸ il_mem_inj₀.mpr ha) il_mem_inj₁
  · rw [inj₁_injective heq]; exact hY'

end Exercise619

end DomainTheory.NeighbourhoodSystems
