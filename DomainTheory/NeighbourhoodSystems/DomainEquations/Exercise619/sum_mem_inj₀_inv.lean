/-ai
If the left injection of a set is a neighbourhood of the abstract sum, then that set is a neighbourhood of the first system.

The sum master contains the untagged token, which does not lie in a left injection, so the neighbourhood is not the master. A right injection of a nonempty neighbourhood contains a right-tagged token, which does not lie in a left injection. The remaining case is a left injection of a neighbourhood of the first system, and injectivity of the left injection identifies the set with that neighbourhood.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example62 ExampleB

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

theorem sum_mem_inj₀_inv {X : Set Str} (h : (sum D₀ D₁ h₀ h₁).mem (inj₀ X)) : D₀.mem X := by
  rcases h with h0 | ⟨X', hX', heq⟩ | ⟨Y', hY', heq⟩
  · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₀
  · rw [inj₀_injective heq]; exact hX'
  · obtain ⟨b, hb⟩ := h₁ Y' hY'
    exact absurd (heq ▸ ir_mem_inj₁.mpr hb) ir_mem_inj₀

end Exercise619

end DomainTheory.NeighbourhoodSystems
