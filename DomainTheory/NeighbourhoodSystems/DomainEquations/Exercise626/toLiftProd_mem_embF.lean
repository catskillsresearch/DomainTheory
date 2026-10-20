module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.embF_ne_liftTokMaster
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.lift
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.mem_liftBot
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.mem_liftUp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.toSumLift_mem_embF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.toSumLift_mem_embT
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.fromSumLift_mem_embFF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.fromSumLift_mem_embTF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.toLiftProd

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

@[simp] theorem toLiftProd_mem_embF {z : (D.lift.otimes E.lift).sys.Element} {X Y : Set Str}
    (hX : D.sys.mem X) (hY : E.sys.mem Y) :
    (toLiftProd z).mem (embBit false (prodTokNbhd X Y)) ↔
      z.mem (prodTokNbhd (embBit false X) (embBit false Y)) := by
  constructor
  · rintro (h0 | ⟨X', Y', hX', hY', heq, hz⟩)
    · exact absurd h0 (embF_ne_liftTokMaster (D := prodTok D.sys E.sys))
    · obtain ⟨rfl, rfl⟩ := prodTokNbhd_injective (embBit_injective heq); exact hz
  · intro hz; exact Or.inr ⟨X, Y, hX, hY, rfl, hz⟩

end Exercise619

end DomainTheory.NeighbourhoodSystems
