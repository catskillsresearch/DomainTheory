module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.embF_ne_sumTokMaster
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.toSum_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.toSum_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.fromSum

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example62 ExampleB

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

@[simp] theorem fromSum_mem_embF {s : (sum D₀ D₁ h₀ h₁).Element} {X : Set Str} (hX : D₀.mem X) :
    (fromSum s).mem (embBit false X) ↔ s.mem (inj₀ X) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hs⟩ | ⟨Y', hY', heq, hs⟩)
    · exact absurd h0 embF_ne_sumTokMaster
    · rwa [embBit_injective heq]
    · exact absurd heq (embBit_ne (show (false : Bool) ≠ true by decide) (h₀ X hX))
  · intro hs; exact Or.inr (Or.inl ⟨X, hX, rfl, hs⟩)

end Exercise619

end DomainTheory.NeighbourhoodSystems
