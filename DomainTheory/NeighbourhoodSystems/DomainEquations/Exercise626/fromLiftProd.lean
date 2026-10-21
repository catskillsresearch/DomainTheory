/-ai
The inverse comparison from the lift of a product to the smash of the two lifts sends an element s to the element whose neighbourhoods are the product neighbourhood of the two lift masters, together with the rectangles of false-tagged factor neighbourhoods whose product tag lies in s. The neighbourhood-system laws are checked by splitting the master case from the rectangle case, using absorption of a false tag by a lift master and the intersection and upward closure of s.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.liftTokMaster
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.liftTokMaster_inter_embF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.lift
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.mem_liftBot
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.mem_liftUp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.toSumLift_mem_embF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.toSumLift_mem_embT
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.fromSumLift_mem_embFF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.fromSumLift_mem_embTF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.ot_mem_prod
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.lp_mem_embF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.lp_prod_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.toLiftProd_mem_embF

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

/-- The inverse half `|(𝒟 × ℰ)_⊥| → |𝒟_⊥ ⊗ ℰ_⊥|`. -/
def fromLiftProd (s : (D.prod E).lift.sys.Element) : (D.lift.otimes E.lift).sys.Element where
  mem W := W = prodTokNbhd (liftTokMaster D.sys) (liftTokMaster E.sys)
    ∨ (∃ X Y, D.sys.mem X ∧ E.sys.mem Y ∧ W = prodTokNbhd (embBit false X) (embBit false Y) ∧
        s.mem (embBit false (prodTokNbhd X Y)))
  sub := by
    rintro W (rfl | ⟨X, Y, hX, hY, rfl, -⟩)
    · exact Or.inl rfl
    · exact ot_mem_prod hX hY
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, Y, hX, hY, rfl, hsXY⟩) (rfl | ⟨X', Y', hX', hY', rfl, hsXY'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · refine Or.inr ⟨X', Y', hX', hY', ?_, hsXY'⟩
      rw [prodTokNbhd_inter, liftTokMaster_inter_embF hX', liftTokMaster_inter_embF hY']
    · refine Or.inr ⟨X, Y, hX, hY, ?_, hsXY⟩
      rw [Set.inter_comm, prodTokNbhd_inter, liftTokMaster_inter_embF hX,
        liftTokMaster_inter_embF hY]
    · have hs := s.inter_mem hsXY hsXY'
      rw [embBit_inter, prodTokNbhd_inter] at hs
      obtain ⟨hXi, hYi⟩ := lp_prod_inv (s.sub hs)
      refine Or.inr ⟨X ∩ X', Y ∩ Y', hXi, hYi, ?_, hs⟩
      rw [prodTokNbhd_inter, embBit_inter, embBit_inter]
  up_mem := by
    rintro W W' (rfl | ⟨X, Y, hX, hY, rfl, hsXY⟩) hW' hsub
    · exact Or.inl (Set.Subset.antisymm ((D.lift.otimes E.lift).sys.sub_master hW') hsub)
    · rcases hW' with rfl | ⟨U, V, hU, hV, hUne, hVne, rfl⟩
      · exact Or.inl rfl
      · rcases hU with rfl | ⟨X'', hX''D, rfl⟩
        · exact absurd rfl hUne
        · rcases hV with rfl | ⟨Y'', hY''E, rfl⟩
          · exact absurd rfl hVne
          · refine Or.inr ⟨X'', Y'', hX''D, hY''E, rfl, ?_⟩
            obtain ⟨hsX, hsY⟩ := prodTokNbhd_subset_iff.mp hsub
            exact s.up_mem hsXY (lp_mem_embF hX''D hY''E)
              (embBit_subset.mpr (prodTokNbhd_subset_iff.mpr
                ⟨embBit_subset.mp hsX, embBit_subset.mp hsY⟩))

end Exercise619

end DomainTheory.NeighbourhoodSystems
