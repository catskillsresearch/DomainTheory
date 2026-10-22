module

public import DomainTheory.ContinuousLattice.InverseLimits
public import Mathlib.Order.Hom.Basic
public import Mathlib.Topology.Homeomorph.Defs
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.CLat
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.BasicInst5
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.towerType_zero
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.BasicInst8
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.towerToMap_coe
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.conjMap
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.conjMap_apply
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.functionSpaceRetrFun

@[expose] public section

namespace DomainTheory.ContinuousLattice

universe u

attribute [instance] CLat.str

/-- Continuity, for the lattice Scott topologies on the function spaces, of
`g ↦ j ∘ g ∘ i`. -/
theorem functionSpaceRetrFun_outer_continuous {D D' : Type u}
    [CompleteLattice D] [CompleteLattice D']
    (P : IsContinuousLatticeProjection D D') :
    @Continuous (ScottMap D' D') (ScottMap D D)
      scottTopologicalSpace scottTopologicalSpace (functionSpaceRetrFun P) := by
  exact @Continuous.congr (ScottMap D' D') (ScottMap D D)
    scottTopologicalSpace scottTopologicalSpace (conjMap P.retr P.incl).1
    (functionSpaceRetrFun P) (conjMap P.retr P.incl).continuous
    (fun g => ScottMap.ext fun _ => rfl)

end DomainTheory.ContinuousLattice
