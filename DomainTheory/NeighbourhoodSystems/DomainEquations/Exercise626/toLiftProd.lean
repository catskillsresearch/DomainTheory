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
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.ot_mem_prod_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.lp_mem_embF

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

/-- The forward half `|𝒟_⊥ ⊗ ℰ_⊥| → |(𝒟 × ℰ)_⊥|`. -/
def toLiftProd (z : (D.lift.otimes E.lift).sys.Element) : (D.prod E).lift.sys.Element where
  mem W := W = liftTokMaster (prodTok D.sys E.sys)
    ∨ (∃ X Y, D.sys.mem X ∧ E.sys.mem Y ∧ W = embBit false (prodTokNbhd X Y) ∧
        z.mem (prodTokNbhd (embBit false X) (embBit false Y)))
  sub := by
    rintro W (rfl | ⟨X, Y, hX, hY, rfl, -⟩)
    · exact Or.inl rfl
    · exact lp_mem_embF hX hY
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, Y, hX, hY, rfl, hzXY⟩) (rfl | ⟨X', Y', hX', hY', rfl, hzXY'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · refine Or.inr ⟨X', Y', hX', hY', ?_, hzXY'⟩
      rw [liftTokMaster_inter_embF (prodTok_mem_prodTokNbhd hX' hY')]
    · refine Or.inr ⟨X, Y, hX, hY, ?_, hzXY⟩
      rw [Set.inter_comm, liftTokMaster_inter_embF (prodTok_mem_prodTokNbhd hX hY)]
    · have hz := z.inter_mem hzXY hzXY'
      rw [prodTokNbhd_inter, embBit_inter, embBit_inter] at hz
      obtain ⟨hXi, hYi⟩ := ot_mem_prod_inv (z.sub hz)
      refine Or.inr ⟨X ∩ X', Y ∩ Y', hXi, hYi, ?_, hz⟩
      rw [embBit_inter, prodTokNbhd_inter]
  up_mem := by
    rintro W W' (rfl | ⟨X, Y, hX, hY, rfl, hzXY⟩) hW' hsub
    · exact Or.inl (Set.Subset.antisymm ((D.prod E).lift.sys.sub_master hW') hsub)
    · rcases hW' with rfl | ⟨Z, hZ, rfl⟩
      · exact Or.inl rfl
      · obtain ⟨X'', Y'', hX'', hY'', rfl⟩ := hZ
        refine Or.inr ⟨X'', Y'', hX'', hY'', rfl, ?_⟩
        obtain ⟨hsX, hsY⟩ := prodTokNbhd_subset_iff.mp (embBit_subset.mp hsub)
        exact z.up_mem hzXY (ot_mem_prod hX'' hY'')
          (prodTokNbhd_subset_iff.mpr ⟨embBit_subset.mpr hsX, embBit_subset.mpr hsY⟩)

end Exercise619

end DomainTheory.NeighbourhoodSystems
