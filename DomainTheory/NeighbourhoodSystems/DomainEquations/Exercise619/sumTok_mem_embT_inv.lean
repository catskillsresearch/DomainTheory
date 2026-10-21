/-ai
If the true-tagged copy of a set is a neighbourhood of the concrete sum, then that set is a neighbourhood of the second system.

The master contains the empty word, which is not a tagged word, so the neighbourhood is not the master. A false-tagged copy of a nonempty neighbourhood cannot equal a true-tagged copy. The remaining case is a true-tagged copy of a neighbourhood of the second system, and injectivity of the tagging identifies the set with that neighbourhood.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.nil_mem_sumTokMaster
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.sumTok

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example62 ExampleB

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

theorem sumTok_mem_embT_inv {W : Set Str} (h : (sumTok D₀ D₁ h₀ h₁).mem (embBit true W)) :
    D₁.mem W := by
  rcases h with h0 | ⟨X, hX, heq⟩ | ⟨Y, hY, heq⟩
  · exact absurd (h0.symm ▸ nil_mem_sumTokMaster) nil_not_mem_embBit
  · exact absurd heq.symm (embBit_ne (show (false : Bool) ≠ true by decide) (h₀ X hX))
  · rw [embBit_injective heq]; exact hY

end Exercise619

end DomainTheory.NeighbourhoodSystems
