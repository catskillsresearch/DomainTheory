module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gGen_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gTower_zero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gTower_succ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.mem_gColim
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gColim_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.ext
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.BasicInst28
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.id_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.comp_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gFunctor_obj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gFunctorMap_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.descRel_succ

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {A₀ A₁ B₀ B₁ : ScottSys}

/-- **Sum carries the injection.** `(i₀ + i₁) = i` for the sum subsystem: both relate `W ↦ W'` iff
`W ∈ 𝒟₀+𝒟₁`, `W' ∈ ℰ₀+ℰ₁`, `W ⊆ W'`. -/
theorem sumMapTok_inj (h0 : A₀.sys ◁ B₀.sys) (h1 : A₁.sys ◁ B₁.sys) :
    sumMapTok h0.inj h1.inj = (sumTok_subsystem h0 h1).inj := by
  have hsubM : ∀ {W : Set Str}, (A₀.sum A₁).sys.mem W → W ⊆ sumTokMaster B₀.sys B₁.sys := by
    rintro W (rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩)
    · exact (show sumTokMaster A₀.sys A₁.sys = sumTokMaster B₀.sys B₁.sys by
        unfold sumTokMaster; rw [h0.master_eq, h1.master_eq]).subset
    · exact embF_subset_sumTokMaster (h0.sub hX)
    · exact embT_subset_sumTokMaster (h1.sub hY)
  apply ApproximableMap.ext
  intro W W'
  rw [Subsystem.inj_rel]
  constructor
  · rintro (⟨hW, rfl⟩ | ⟨X, X', ⟨hX, hX', hXsub⟩, rfl, rfl⟩ | ⟨Y, Y', ⟨hY, hY', hYsub⟩, rfl, rfl⟩)
    · exact ⟨hW, (B₀.sum B₁).sys.master_mem, hsubM hW⟩
    · exact ⟨Or.inr (Or.inl ⟨X, hX, rfl⟩), Or.inr (Or.inl ⟨X', hX', rfl⟩), embBit_subset.mpr hXsub⟩
    · exact ⟨Or.inr (Or.inr ⟨Y, hY, rfl⟩), Or.inr (Or.inr ⟨Y', hY', rfl⟩), embBit_subset.mpr hYsub⟩
  · rintro ⟨hW, hW', hsub⟩
    rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
    · exact Or.inl ⟨hW, rfl⟩
    · rcases hW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
      · exact absurd (hsub nil_mem_sumTokMaster) nil_not_mem_embBit
      · exact Or.inr (Or.inl ⟨X, X', ⟨hX, hX', embBit_subset.mp hsub⟩, rfl, rfl⟩)
      · exact absurd hsub (fun h => embBit_not_subset_cross (by decide) (A₁.ne Y hY) h)
    · rcases hW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
      · exact absurd (hsub nil_mem_sumTokMaster) nil_not_mem_embBit
      · exact absurd hsub (fun h => embBit_not_subset_cross (by decide) (A₀.ne X hX) h)
      · exact Or.inr (Or.inr ⟨Y, Y', ⟨hY, hY', embBit_subset.mp hsub⟩, rfl, rfl⟩)

end Exercise619

end DomainTheory.NeighbourhoodSystems
