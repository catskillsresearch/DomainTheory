module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.lift
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.mem_liftBot
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.mem_liftUp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.toSumLift_mem_embF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.toSumLift_mem_embT
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.fromSumLift_mem_embFF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.fromSumLift_mem_embTF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.toLiftProd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.toLiftProd_mem_embF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.fromLiftProd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.fromLiftProd_mem_prod

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

theorem fromLiftProd_toLiftProd (z : (D.lift.otimes E.lift).sys.Element) :
    fromLiftProd (toLiftProd z) = z := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨X, Y, hX, hY, rfl, hs⟩)
    · exact z.master_mem
    · exact (toLiftProd_mem_embF hX hY).mp hs
  · intro hW
    rcases z.sub hW with rfl | ⟨X, Y, hX, hY, hXne, hYne, rfl⟩
    · exact Or.inl rfl
    · rcases hX with rfl | ⟨X'', hX''D, rfl⟩
      · exact absurd rfl hXne
      · rcases hY with rfl | ⟨Y'', hY''E, rfl⟩
        · exact absurd rfl hYne
        · exact Or.inr ⟨X'', Y'', hX''D, hY''E, rfl, (toLiftProd_mem_embF hX''D hY''E).mpr hW⟩

end Exercise619

end DomainTheory.NeighbourhoodSystems
