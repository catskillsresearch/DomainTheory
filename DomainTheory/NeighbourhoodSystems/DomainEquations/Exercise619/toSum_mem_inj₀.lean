/-ai
For a neighbourhood X of the first system, the left injection of X belongs to the forward image of a token element if and only if that element contains the false-tagged copy of X.

In the forward direction the master clause is impossible, because the untagged token of the master does not lie in a left injection, and the right-injection clause is impossible, because a nonempty neighbourhood supplies a left-tagged token of the left injection, which does not lie in a right injection. The remaining clause is a left injection of some neighbourhood, and injectivity identifies it with X. Conversely, the left-injection clause of the forward image applies directly.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.sumTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.toSum

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example62 ExampleB

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

@[simp] theorem toSum_mem_inj₀ {x : (sumTok D₀ D₁ h₀ h₁).Element} {X : Set Str} (hX : D₀.mem X) :
    (toSum x).mem (inj₀ X) ↔ x.mem (embBit false X) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hz⟩ | ⟨Y', hY', heq, hz⟩)
    · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₀
    · rwa [inj₀_injective heq]
    · obtain ⟨a, ha⟩ := h₀ X hX
      exact absurd (heq ▸ il_mem_inj₀.mpr ha) il_mem_inj₁
  · intro hz; exact Or.inr (Or.inl ⟨X, hX, rfl, hz⟩)

end Exercise619

end DomainTheory.NeighbourhoodSystems
