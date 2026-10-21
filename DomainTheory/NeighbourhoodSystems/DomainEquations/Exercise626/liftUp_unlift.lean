/-ai
If an element z of the lift contains the false tag of the master of D, then lifting the unlift of z returns z.

Element extensionality compares an arbitrary set W. The lift master in the composite is the master of z, and a false-tagged neighbourhood of the unlift is already a neighbourhood of z. Conversely, downward closure of z splits a neighbourhood into the master, recorded as the left disjunct, or a false-tagged neighbourhood, recorded together with the original membership.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB
open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {D : NeighborhoodSystem Str}










variable {hD : ∀ X, D.mem X → X.Nonempty}









theorem liftUp_unlift (z : (liftTok D hD).Element) (hz : z.mem (embBit false D.master)) :
    liftUp (hD := hD) (unlift z hz) = z := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨X, hX, rfl⟩)
    · exact z.master_mem
    · exact hX
  · intro hW
    rcases z.sub hW with rfl | ⟨X, hX, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨X, hW, rfl⟩

end Exercise619
end DomainTheory.NeighbourhoodSystems
