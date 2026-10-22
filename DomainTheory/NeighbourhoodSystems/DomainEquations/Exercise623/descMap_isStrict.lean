module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gGen_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gTower_zero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gTower_succ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.mem_gColim
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gColim_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.BasicInst28
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.id_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.comp_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gFunctor_obj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gFunctorMap_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.descRel_succ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.descRel_isStrict
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.descMap
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.TexpF

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

section Existence

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master) (B : TAlgebra (TexpF N))

/-- `val` is strict (a union of strict maps). -/
theorem descMap_isStrict : IsStrict (descMap hN B) := by
  rintro Y ⟨n, hn⟩
  exact descRel_isStrict hN B n hn

end Existence

end Exercise619

end DomainTheory.NeighbourhoodSystems
