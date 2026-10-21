/-ai
The smash product carries the projection. If one neighbourhood system is a subsystem of another and a second pair stands in the same relation, the smash-product map of the two projections equals the projection of the smash-product subsystem.

By extensionality of approximable maps it is enough to compare relations. A master step is sent to the master of the smaller smash, with the inclusion rewritten through the master equalities or through the factor inclusions into the masters, and a proper smash step is the product-token inclusion of the factor inclusions. In the other direction a master target is the master case. A proper target against a master source would force a proper factor of the smaller system to equal its master. Two proper neighbourhoods split into the two factor inclusions.
ai-/
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

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {A₀ A₁ B₀ B₁ : ScottSys}

/-- **Smash product carries the projection.** -/
theorem otimesMapTok_proj (h0 : A₀.sys ◁ B₀.sys) (h1 : A₁.sys ◁ B₁.sys) :
    otimesMapTok h0.proj h1.proj = (otimesTok_subsystem h0 h1).proj := by
  apply ApproximableMap.ext
  intro W W'
  rw [Subsystem.proj_rel]
  constructor
  · rintro (⟨hW, rfl⟩ |
      ⟨X, Y, X', Y', ⟨hX, hX', hXs⟩, ⟨hY, hY', hYs⟩, hXne, hYne, hX'ne, hY'ne, rfl, rfl⟩)
    · refine ⟨hW, (A₀.otimes A₁).sys.master_mem, ?_⟩
      rcases hW with rfl | ⟨P, Q, hP, hQ, hPne, hQne, rfl⟩
      · exact (show prodTokNbhd B₀.sys.master B₁.sys.master
            = prodTokNbhd A₀.sys.master A₁.sys.master by rw [h0.master_eq, h1.master_eq]).subset
      · exact prodTokNbhd_subset_iff.mpr ⟨by rw [h0.master_eq]; exact B₀.sys.sub_master hP,
          by rw [h1.master_eq]; exact B₁.sys.sub_master hQ⟩
    · exact ⟨Or.inr ⟨X, Y, hX, hY, hXne, hYne, rfl⟩, Or.inr ⟨X', Y', hX', hY', hX'ne, hY'ne, rfl⟩,
        prodTokNbhd_subset_iff.mpr ⟨hXs, hYs⟩⟩
  · rintro ⟨hW, hW', hsub⟩
    rcases hW' with rfl | ⟨X', Y', hX', hY', hX'ne, hY'ne, rfl⟩
    · exact Or.inl ⟨hW, rfl⟩
    · rcases hW with rfl | ⟨X, Y, hX, hY, hXne, hYne, rfl⟩
      · obtain ⟨hsX, _⟩ := prodTokNbhd_subset_iff.mp hsub
        exact absurd (Set.Subset.antisymm (A₀.sys.sub_master hX')
          (by rw [h0.master_eq]; exact hsX)) hX'ne
      · obtain ⟨hXs, hYs⟩ := prodTokNbhd_subset_iff.mp hsub
        exact Or.inr ⟨X, Y, X', Y', ⟨hX, hX', hXs⟩, ⟨hY, hY', hYs⟩,
          hXne, hYne, hX'ne, hY'ne, rfl, rfl⟩

end Exercise619

end DomainTheory.NeighbourhoodSystems
