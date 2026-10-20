module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.lift
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.mem_liftBot
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.mem_liftUp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.toSumLift
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.toSumLift_mem_embF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.toSumLift_mem_embT
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.fromSumLift
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.fromSumLift_mem_embFF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.fromSumLift_mem_embTF

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

theorem fromSumLift_toSumLift (z : (D.lift.oplus E.lift).sys.Element) :
    fromSumLift (toSumLift z) = z := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨X, hX, rfl, hs⟩ | ⟨Y, hY, rfl, hs⟩)
    · exact z.master_mem
    · exact (toSumLift_mem_embF hX).mp hs
    · exact (toSumLift_mem_embT hY).mp hs
  · intro hW
    rcases z.sub hW with rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩
    · exact Or.inl rfl
    · rcases hX with rfl | ⟨X', hX'D, rfl⟩
      · exact absurd rfl hXne
      · exact Or.inr (Or.inl ⟨X', hX'D, rfl, (toSumLift_mem_embF hX'D).mpr hW⟩)
    · rcases hY with rfl | ⟨Y', hY'E, rfl⟩
      · exact absurd rfl hYne
      · exact Or.inr (Or.inr ⟨Y', hY'E, rfl, (toSumLift_mem_embT hY'E).mpr hW⟩)

end Exercise619

end DomainTheory.NeighbourhoodSystems
