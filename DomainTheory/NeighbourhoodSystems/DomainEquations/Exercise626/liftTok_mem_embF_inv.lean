module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.nil_mem_liftTokMaster
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.liftTok

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {D : NeighborhoodSystem Str}

variable {hD : ∀ X, D.mem X → X.Nonempty}

theorem liftTok_mem_embF_inv {W : Set Str} (h : (liftTok D hD).mem (embBit false W)) : D.mem W := by
  rcases h with h0 | ⟨X, hX, heq⟩
  · exact absurd (h0.symm ▸ nil_mem_liftTokMaster) nil_not_mem_embBit
  · rw [embBit_injective heq]; exact hX

end Exercise619

end DomainTheory.NeighbourhoodSystems
