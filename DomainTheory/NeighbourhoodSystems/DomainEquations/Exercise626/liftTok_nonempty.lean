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

theorem liftTok_nonempty (hD : ∀ X, D.mem X → X.Nonempty) :
    ∀ W, (liftTok D hD).mem W → W.Nonempty := by
  rintro W (rfl | ⟨X, hX, rfl⟩)
  · exact ⟨[], nil_mem_liftTokMaster⟩
  · exact embBit_nonempty (hD X hX)

end Exercise619

end DomainTheory.NeighbourhoodSystems
