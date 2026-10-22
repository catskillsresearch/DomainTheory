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

/-- **Product carries the injection.** -/
theorem prodMapTok_inj (h0 : A₀.sys ◁ B₀.sys) (h1 : A₁.sys ◁ B₁.sys) :
    prodMapTok h0.inj h1.inj = (prodTok_subsystem h0 h1).inj := by
  apply ApproximableMap.ext
  intro W W'
  rw [Subsystem.inj_rel]
  constructor
  · rintro ⟨X, Y, X', Y', ⟨hX, hX', hXs⟩, ⟨hY, hY', hYs⟩, rfl, rfl⟩
    exact ⟨prodTok_mem_prodTokNbhd hX hY, prodTok_mem_prodTokNbhd hX' hY',
      prodTokNbhd_subset_iff.mpr ⟨hXs, hYs⟩⟩
  · rintro ⟨⟨X, Y, hX, hY, rfl⟩, ⟨X', Y', hX', hY', rfl⟩, hsub⟩
    obtain ⟨hXs, hYs⟩ := prodTokNbhd_subset_iff.mp hsub
    exact ⟨X, Y, X', Y', ⟨hX, hX', hXs⟩, ⟨hY, hY', hYs⟩, rfl, rfl⟩

end Exercise619

end DomainTheory.NeighbourhoodSystems
