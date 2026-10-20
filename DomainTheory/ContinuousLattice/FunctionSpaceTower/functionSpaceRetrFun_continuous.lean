module

public import DomainTheory.ContinuousLattice.InverseLimits
public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import Mathlib.Topology.Homeomorph.Defs
import all Mathlib.Topology.Homeomorph.Defs
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.CLat
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.BasicInst5
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.towerType_zero
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.BasicInst8
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.towerToMap_coe
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.conjMap_apply

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.ContinuousLattice

universe u

attribute [instance] CLat.str

/-- Continuity of the inner map `j ∘ g ∘ i`. -/
theorem functionSpaceRetrFun_continuous {D D' : Type u}
    [CompleteLattice D] [CompleteLattice D']
    (P : IsContinuousLatticeProjection D D') (g : ScottMap D' D') :
    @Continuous D D scottTopologicalSpace scottTopologicalSpace
      (fun x => P.retr (g (P.incl x))) :=
  @Continuous.congr D D scottTopologicalSpace scottTopologicalSpace
    (P.retr.comp (g.comp P.incl)).1 (fun x => P.retr (g (P.incl x)))
    (P.retr.comp (g.comp P.incl)).continuous (fun _ => rfl)

end DomainTheory.ContinuousLattice
