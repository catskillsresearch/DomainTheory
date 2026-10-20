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

/-- Continuity of the inner map `i ∘ f ∘ j`. -/
theorem functionSpaceInclFun_continuous {D D' : Type u}
    [CompleteLattice D] [CompleteLattice D']
    (P : IsContinuousLatticeProjection D D') (f : ScottMap D D) :
    @Continuous D' D' scottTopologicalSpace scottTopologicalSpace
      (fun x => P.incl (f (P.retr x))) :=
  @Continuous.congr D' D' scottTopologicalSpace scottTopologicalSpace
    (P.incl.comp (f.comp P.retr)).1 (fun x => P.incl (f (P.retr x)))
    (P.incl.comp (f.comp P.retr)).continuous (fun _ => rfl)

end DomainTheory.ContinuousLattice
