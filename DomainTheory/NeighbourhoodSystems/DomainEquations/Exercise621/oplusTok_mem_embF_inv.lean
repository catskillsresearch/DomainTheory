/-ai
If the false tag of W belongs to the coalesced sum, then W belongs to the left system.

The master clause would place the empty string in a bit embedding. A left tag gives W by injectivity of the bit embedding. A right tag equates opposite bits.
ai-/
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


theorem oplusTok_mem_embF_inv {W : Set Str} (h : (oplusTok D₀ D₁ h₀ h₁).mem (embBit false W)) :
    D₀.mem W := by
  rcases h with h0 | ⟨X, hX, -, heq⟩ | ⟨Y, hY, -, heq⟩
  · exact absurd (h0.symm ▸ nil_mem_sumTokMaster) nil_not_mem_embBit
  · rw [embBit_injective heq]; exact hX
  · exact absurd heq.symm (embBit_ne (show (true : Bool) ≠ false by decide) (h₁ Y hY))

end Exercise619
end DomainTheory.NeighbourhoodSystems
