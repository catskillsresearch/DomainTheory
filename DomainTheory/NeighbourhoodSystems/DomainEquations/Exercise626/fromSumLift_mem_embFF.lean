module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.mem_liftBot
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.mem_liftUp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.toSumLift_mem_embF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.toSumLift_mem_embT
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.fromSumLift

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {D : NeighborhoodSystem Str}

variable {hD : ∀ X, D.mem X → X.Nonempty}

variable {A B C : ScottSys}

variable {D E : ScottSys}

@[simp] theorem fromSumLift_mem_embFF {s : (D.sum E).sys.Element} {X : Set Str} (hX : D.sys.mem X) :
    (fromSumLift s).mem (embBit false (embBit false X)) ↔ s.mem (embBit false X) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hs⟩ | ⟨Y', hY', heq, hs⟩)
    · exact absurd h0 embF_ne_sumTokMaster
    · rwa [embBit_injective (embBit_injective heq)]
    · exact absurd heq (embBit_ne (show (false : Bool) ≠ true by decide)
        (embBit_nonempty (D.ne X hX)))
  · intro hs; exact Or.inr (Or.inl ⟨X, hX, rfl, hs⟩)

end Exercise619

end DomainTheory.NeighbourhoodSystems
