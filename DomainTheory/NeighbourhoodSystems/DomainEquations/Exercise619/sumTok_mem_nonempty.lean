/-ai
Every neighbourhood of the concrete token sum is nonempty.

The master contains the empty word. A false-tagged copy of a neighbourhood of the first system is nonempty because that neighbourhood is nonempty, and a true-tagged copy of a neighbourhood of the second system is nonempty for the same reason.
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

theorem sumTok_mem_nonempty {W : Set Str} (h : (sumTok D₀ D₁ h₀ h₁).mem W) : W.Nonempty := by
  rcases h with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
  · exact ⟨[], nil_mem_sumTokMaster⟩
  · exact embBit_nonempty (h₀ X hX)
  · exact embBit_nonempty (h₁ Y hY)

end Exercise619

end DomainTheory.NeighbourhoodSystems
