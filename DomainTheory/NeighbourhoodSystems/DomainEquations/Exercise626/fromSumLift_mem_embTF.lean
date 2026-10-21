/-ai
The image under the inverse sum comparison contains the true-then-false tag of a right neighbourhood Y if and only if the source contains the single true tag of Y.

The master case conflicts with a true tag differing from the sum master. A false-side witness conflicts with inequality of the two tags on a nonempty set. A true-side witness rewrites by injectivity of tagging. The converse records the right clause of the definition.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.mem_liftBot
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.mem_liftUp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.toSumLift_mem_embF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.toSumLift_mem_embT
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.fromSumLift
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.fromSumLift_mem_embFF

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {D : NeighborhoodSystem Str}

variable {hD : ∀ X, D.mem X → X.Nonempty}

variable {A B C : ScottSys}

variable {D E : ScottSys}

@[simp] theorem fromSumLift_mem_embTF {s : (D.sum E).sys.Element} {Y : Set Str} (hY : E.sys.mem Y) :
    (fromSumLift s).mem (embBit true (embBit false Y)) ↔ s.mem (embBit true Y) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hs⟩ | ⟨Y', hY', heq, hs⟩)
    · exact absurd h0 embT_ne_sumTokMaster
    · exact absurd heq (embBit_ne (show (true : Bool) ≠ false by decide)
        (embBit_nonempty (E.ne Y hY)))
    · rwa [embBit_injective (embBit_injective heq)]
  · intro hs; exact Or.inr (Or.inr ⟨Y, hY, rfl, hs⟩)

end Exercise619

end DomainTheory.NeighbourhoodSystems
