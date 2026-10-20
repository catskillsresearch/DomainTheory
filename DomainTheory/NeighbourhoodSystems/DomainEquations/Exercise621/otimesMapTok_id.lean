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




/-- **`(I ⊗ I) = I`.** -/
theorem otimesMapTok_id :
    otimesMapTok (idMap A₀.sys) (idMap A₁.sys) = idMap (A₀.otimes A₁).sys := by
  apply ApproximableMap.ext
  intro W W'
  constructor
  · rintro (⟨hW, rfl⟩ | ⟨X, Y, X', Y', ⟨hX, hX', hsubX⟩, ⟨hY, hY', hsubY⟩,
      hXne, hYne, hX'ne, hY'ne, rfl, rfl⟩)
    · exact ⟨hW, (A₀.otimes A₁).sys.master_mem, (A₀.otimes A₁).sys.sub_master hW⟩
    · exact ⟨otimesTok_mem_prod hX hY hXne hYne, otimesTok_mem_prod hX' hY' hX'ne hY'ne,
        prodTokNbhd_subset_iff.mpr ⟨hsubX, hsubY⟩⟩
  · rintro ⟨hW, hW', hsub⟩
    rcases hW' with rfl | ⟨X', Y', hX', hY', hX'ne, hY'ne, rfl⟩
    · exact Or.inl ⟨hW, rfl⟩
    · rcases hW with rfl | ⟨X, Y, hX, hY, hXne, hYne, rfl⟩
      · obtain ⟨hsubX, -⟩ := prodTokNbhd_subset_iff.mp hsub
        exact absurd (Set.Subset.antisymm (A₀.sys.sub_master hX') hsubX) hX'ne
      · obtain ⟨hsX, hsY⟩ := prodTokNbhd_subset_iff.mp hsub
        exact Or.inr ⟨X, Y, X', Y', ⟨hX, hX', hsX⟩, ⟨hY, hY', hsY⟩,
          hXne, hYne, hX'ne, hY'ne, rfl, rfl⟩

end Exercise619
end DomainTheory.NeighbourhoodSystems
