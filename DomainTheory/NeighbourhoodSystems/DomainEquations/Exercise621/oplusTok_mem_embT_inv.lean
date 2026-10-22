module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB
open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


theorem oplusTok_mem_embT_inv {W : Set Str} (h : (oplusTok D₀ D₁ h₀ h₁).mem (embBit true W)) :
    D₁.mem W := by
  rcases h with h0 | ⟨X, hX, -, heq⟩ | ⟨Y, hY, -, heq⟩
  · exact absurd (h0.symm ▸ nil_mem_sumTokMaster) nil_not_mem_embBit
  · exact absurd heq.symm (embBit_ne (show (false : Bool) ≠ true by decide) (h₀ X hX))
  · rw [embBit_injective heq]; exact hY

end Exercise619
end DomainTheory.NeighbourhoodSystems
