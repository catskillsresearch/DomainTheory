module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB
open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}




variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}














variable {A₀ A₁ B₀ B₁ : ScottSys}


variable {C₀ C₁ : ScottSys}


/-- **`(I ⊕ I) = I`.** -/
theorem oplusMapTok_id :
    oplusMapTok (idMap A₀.sys) (idMap A₁.sys) = idMap (A₀.oplus A₁).sys := by
  apply ApproximableMap.ext
  intro W W'
  constructor
  · rintro (⟨hW, rfl⟩ | ⟨X, X', ⟨hX, hX', hsub⟩, hXne, hX'ne, rfl, rfl⟩ |
      ⟨Y, Y', ⟨hY, hY', hsub⟩, hYne, hY'ne, rfl, rfl⟩)
    · exact ⟨hW, (A₀.oplus A₁).sys.master_mem, (A₀.oplus A₁).sys.sub_master hW⟩
    · exact ⟨oplusTok_mem_embF (h₀ := A₀.ne) (h₁ := A₁.ne) hX hXne,
        oplusTok_mem_embF (h₀ := A₀.ne) (h₁ := A₁.ne) hX' hX'ne, embBit_subset.mpr hsub⟩
    · exact ⟨oplusTok_mem_embT (h₀ := A₀.ne) (h₁ := A₁.ne) hY hYne,
        oplusTok_mem_embT (h₀ := A₀.ne) (h₁ := A₁.ne) hY' hY'ne, embBit_subset.mpr hsub⟩
  · rintro ⟨hW, hW', hsub⟩
    rcases hW' with rfl | ⟨X', hX', hX'ne, rfl⟩ | ⟨Y', hY', hY'ne, rfl⟩
    · exact Or.inl ⟨hW, rfl⟩
    · rcases hW with rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩
      · exact absurd (hsub nil_mem_sumTokMaster) nil_not_mem_embBit
      · exact Or.inr (Or.inl ⟨X, X', ⟨hX, hX', embBit_subset.mp hsub⟩, hXne, hX'ne, rfl, rfl⟩)
      · exact absurd hsub (fun h => embBit_not_subset_cross (by decide) (A₁.ne Y hY) h)
    · rcases hW with rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩
      · exact absurd (hsub nil_mem_sumTokMaster) nil_not_mem_embBit
      · exact absurd hsub (fun h => embBit_not_subset_cross (by decide) (A₀.ne X hX) h)
      · exact Or.inr (Or.inr ⟨Y, Y', ⟨hY, hY', embBit_subset.mp hsub⟩, hYne, hY'ne, rfl, rfl⟩)

end Exercise619
end DomainTheory.NeighbourhoodSystems
