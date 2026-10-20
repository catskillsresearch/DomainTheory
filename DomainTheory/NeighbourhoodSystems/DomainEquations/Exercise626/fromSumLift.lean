module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.lift
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.liftTok_mem_embF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.mem_liftBot
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.mem_liftUp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.o_mem_embFF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.o_mem_embTF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.toSumLift_mem_embF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.toSumLift_mem_embT

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

/-- The inverse half `|𝒟 + ℰ| → |𝒟_⊥ ⊕ ℰ_⊥|`: reinstate the inner `0`. -/
def fromSumLift (s : (D.sum E).sys.Element) : (D.lift.oplus E.lift).sys.Element where
  mem W := W = sumTokMaster D.lift.sys E.lift.sys
    ∨ (∃ X, D.sys.mem X ∧ W = embBit false (embBit false X) ∧ s.mem (embBit false X))
    ∨ (∃ Y, E.sys.mem Y ∧ W = embBit true (embBit false Y) ∧ s.mem (embBit true Y))
  sub := by
    rintro W (rfl | ⟨X, hX, rfl, -⟩ | ⟨Y, hY, rfl, -⟩)
    · exact Or.inl rfl
    · exact o_mem_embFF hX
    · exact o_mem_embTF hY
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hsX⟩ | ⟨Y, hY, rfl, hsY⟩)
      (rfl | ⟨X', hX', rfl, hsX'⟩ | ⟨Y', hY', rfl, hsY'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · refine Or.inr (Or.inl ⟨X', hX', ?_, hsX'⟩)
      rw [sumTokMaster_inter_embF (D₀ := D.lift.sys) (D₁ := E.lift.sys)
        (liftTok_mem_embF (hD := D.ne) hX')]
    · refine Or.inr (Or.inr ⟨Y', hY', ?_, hsY'⟩)
      rw [sumTokMaster_inter_embT (D₀ := D.lift.sys) (D₁ := E.lift.sys)
        (liftTok_mem_embF (hD := E.ne) hY')]
    · refine Or.inr (Or.inl ⟨X, hX, ?_, hsX⟩)
      rw [Set.inter_comm, sumTokMaster_inter_embF (D₀ := D.lift.sys) (D₁ := E.lift.sys)
        (liftTok_mem_embF (hD := D.ne) hX)]
    · refine Or.inr (Or.inl ⟨X ∩ X', ?_, by rw [embBit_inter, embBit_inter], ?_⟩)
      · have hs := s.inter_mem hsX hsX'; rw [embBit_inter] at hs
        exact sumTok_mem_embF_inv (h₀ := D.ne) (h₁ := E.ne) (s.sub hs)
      · have hs := s.inter_mem hsX hsX'; rwa [embBit_inter] at hs
    · exfalso
      have hs := s.inter_mem hsX hsY'
      rw [embBit_inter_ne (show (false : Bool) ≠ true by decide)] at hs
      obtain ⟨t, ht⟩ := sumTok_mem_nonempty (h₀ := D.ne) (h₁ := E.ne) (s.sub hs)
      exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr ⟨Y, hY, ?_, hsY⟩)
      rw [Set.inter_comm, sumTokMaster_inter_embT (D₀ := D.lift.sys) (D₁ := E.lift.sys)
        (liftTok_mem_embF (hD := E.ne) hY)]
    · exfalso
      have hs := s.inter_mem hsY hsX'
      rw [embBit_inter_ne (show (true : Bool) ≠ false by decide)] at hs
      obtain ⟨t, ht⟩ := sumTok_mem_nonempty (h₀ := D.ne) (h₁ := E.ne) (s.sub hs)
      exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr ⟨Y ∩ Y', ?_, by rw [embBit_inter, embBit_inter], ?_⟩)
      · have hs := s.inter_mem hsY hsY'; rw [embBit_inter] at hs
        exact sumTok_mem_embT_inv (h₀ := D.ne) (h₁ := E.ne) (s.sub hs)
      · have hs := s.inter_mem hsY hsY'; rwa [embBit_inter] at hs
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hsX⟩ | ⟨Y, hY, rfl, hsY⟩) hW' hsub
    · exact Or.inl (Set.Subset.antisymm ((D.lift.oplus E.lift).sys.sub_master hW') hsub)
    · rcases hW' with rfl | ⟨V, hV, hVne, rfl⟩ | ⟨V, hV, hVne, rfl⟩
      · exact Or.inl rfl
      · rcases hV with rfl | ⟨X'', hX''D, rfl⟩
        · exact absurd rfl hVne
        · refine Or.inr (Or.inl ⟨X'', hX''D, rfl, ?_⟩)
          exact s.up_mem hsX (sumTok_mem_embF (h₀ := D.ne) (h₁ := E.ne) hX''D)
            (embBit_subset.mpr (embBit_subset.mp (embBit_subset.mp hsub)))
      · exact absurd hsub
          (fun hs => embBit_not_subset_cross (show (false : Bool) ≠ true by decide)
            (embBit_nonempty (D.ne X hX)) hs)
    · rcases hW' with rfl | ⟨V, hV, hVne, rfl⟩ | ⟨V, hV, hVne, rfl⟩
      · exact Or.inl rfl
      · exact absurd hsub
          (fun hs => embBit_not_subset_cross (show (true : Bool) ≠ false by decide)
            (embBit_nonempty (E.ne Y hY)) hs)
      · rcases hV with rfl | ⟨Y'', hY''E, rfl⟩
        · exact absurd rfl hVne
        · refine Or.inr (Or.inr ⟨Y'', hY''E, rfl, ?_⟩)
          exact s.up_mem hsY (sumTok_mem_embT (h₀ := D.ne) (h₁ := E.ne) hY''E)
            (embBit_subset.mpr (embBit_subset.mp (embBit_subset.mp hsub)))

end Exercise619

end DomainTheory.NeighbourhoodSystems
