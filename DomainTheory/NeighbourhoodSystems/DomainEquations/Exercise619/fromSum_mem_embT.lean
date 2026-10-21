/-ai
For a neighbourhood Y of the second system, the true-tagged copy of Y belongs to the inverse image of an abstract sum element if and only if the right injection of Y belongs to that element.

In the forward direction the master clause is impossible, because a true-tagged copy is not the sum master, and the false-tagged clause is impossible, because the two tags differ on a nonempty set. The remaining clause is a true-tagged copy of some neighbourhood, and injectivity of the tagging identifies it with Y. Conversely, the true-tagged clause of the inverse image applies directly.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.embT_ne_sumTokMaster
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.toSum_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.toSum_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.fromSum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.fromSum_mem_embF

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example62 ExampleB

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

@[simp] theorem fromSum_mem_embT {s : (sum D₀ D₁ h₀ h₁).Element} {Y : Set Str} (hY : D₁.mem Y) :
    (fromSum s).mem (embBit true Y) ↔ s.mem (inj₁ Y) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hs⟩ | ⟨Y', hY', heq, hs⟩)
    · exact absurd h0 embT_ne_sumTokMaster
    · exact absurd heq.symm (embBit_ne (show (false : Bool) ≠ true by decide) (h₀ X' hX'))
    · rwa [embBit_injective heq]
  · intro hs; exact Or.inr (Or.inr ⟨Y, hY, rfl, hs⟩)

end Exercise619

end DomainTheory.NeighbourhoodSystems
