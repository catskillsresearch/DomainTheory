/-ai
The order isomorphism from elements of the smash of two lifts to elements of the lift of the product is the forward rectangle map, inverted by the map that rebuilds rectangles, with the two round trips given by the corresponding identity lemmas. An inequality of smash elements is equivalent to the inequality of their images because a smash neighbourhood is the master or a proper rectangle of false-tagged factors, rectangle membership is the membership lemma for the forward map, and a neighbourhood of an image is the master or a tagged product neighbourhood transferred by the inequality.
ai-/
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
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.fromLiftProd_toLiftProd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.toLiftProd_fromLiftProd

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

/-- The order-isomorphism `|𝒟_⊥ ⊗ ℰ_⊥| ≃o |(𝒟 × ℰ)_⊥|`. -/
def liftProdEquiv : (D.lift.otimes E.lift).sys.Element ≃o (D.prod E).lift.sys.Element where
  toFun := toLiftProd
  invFun := fromLiftProd
  left_inv := fromLiftProd_toLiftProd
  right_inv := toLiftProd_fromLiftProd
  map_rel_iff' := by
    intro z z'
    constructor
    · intro h W hW
      rcases z.sub hW with rfl | ⟨X, Y, hX, hY, hXne, hYne, rfl⟩
      · exact z'.master_mem
      · rcases hX with rfl | ⟨X'', hX''D, rfl⟩
        · exact absurd rfl hXne
        · rcases hY with rfl | ⟨Y'', hY''E, rfl⟩
          · exact absurd rfl hYne
          · exact (toLiftProd_mem_embF hX''D hY''E).mp
              (h _ ((toLiftProd_mem_embF hX''D hY''E).mpr hW))
    · intro h W hW
      rcases hW with rfl | ⟨X, Y, hX, hY, rfl, hzXY⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨X, Y, hX, hY, rfl, h _ hzXY⟩

end Exercise619

end DomainTheory.NeighbourhoodSystems
