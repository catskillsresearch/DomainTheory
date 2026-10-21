/-ai
The order isomorphism from the elements of the coalesced sum of the lifts of D and E to the elements of the separated sum is toSumLift, with inverse fromSumLift. The two round trips are the corresponding cancellation lemmas. In one direction of the order law, a neighbourhood of the smaller coalesced element is the master, a proper left copy, or a proper right copy. The master belongs to the larger image. An inner lift master is excluded by the properness witness, and a proper false-tagged neighbourhood is carried across by the left or right membership characterization of toSumLift. In the other direction, a neighbourhood of the image is the sum master, a left tag, or a right tag, and the inequality of the images rebuilds the corresponding coalesced membership.
ai-/
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
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.fromSumLift_toSumLift
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.toSumLift_fromSumLift

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

/-- The order-isomorphism `|𝒟_⊥ ⊕ ℰ_⊥| ≃o |𝒟 + ℰ|`. -/
def sumLiftEquiv : (D.lift.oplus E.lift).sys.Element ≃o (D.sum E).sys.Element where
  toFun := toSumLift
  invFun := fromSumLift
  left_inv := fromSumLift_toSumLift
  right_inv := toSumLift_fromSumLift
  map_rel_iff' := by
    intro z z'
    constructor
    · intro h W hW
      rcases z.sub hW with rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩
      · exact z'.master_mem
      · rcases hX with rfl | ⟨X', hX'D, rfl⟩
        · exact absurd rfl hXne
        · exact (toSumLift_mem_embF hX'D).mp (h _ ((toSumLift_mem_embF hX'D).mpr hW))
      · rcases hY with rfl | ⟨Y', hY'E, rfl⟩
        · exact absurd rfl hYne
        · exact (toSumLift_mem_embT hY'E).mp (h _ ((toSumLift_mem_embT hY'E).mpr hW))
    · intro h W hW
      rcases hW with rfl | ⟨X, hX, rfl, hzX⟩ | ⟨Y, hY, rfl, hzY⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨X, hX, rfl, h _ hzX⟩)
      · exact Or.inr (Or.inr ⟨Y, hY, rfl, h _ hzY⟩)

end Exercise619

end DomainTheory.NeighbourhoodSystems
