/-ai
The diagonal specialization of Scott's Proposition 3.7 turns a continuous-lattice projection from D into D' into a continuous-lattice projection from [D → D] into [D' → D']. The inclusion is f ↦ i ∘ f ∘ j and the retraction is g ↦ j ∘ g ∘ i, each bundled with its outer continuity. The retraction-inclusion identity and the inclusion-retraction inequality are the corresponding facts for this diagonal construction.
ai-/
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
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.functionSpaceInclFun
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.functionSpaceInclFun_outer_continuous
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.functionSpaceRetrFun
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.functionSpaceRetrFun_outer_continuous
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.functionSpaceRetrIncl
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.functionSpaceInclRetrLe

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.ContinuousLattice

universe u

attribute [instance] CLat.str

/-- Scott's Proposition 3.7 construction specialized diagonally. -/
noncomputable def functionSpaceProjection
    {D D' : Type u} [CompleteLattice D] [CompleteLattice D']
    (P : IsContinuousLatticeProjection D D') :
    IsContinuousLatticeProjection (ScottMap D D) (ScottMap D' D') where
  incl := ⟨functionSpaceInclFun P, functionSpaceInclFun_outer_continuous P⟩
  retr := ⟨functionSpaceRetrFun P, functionSpaceRetrFun_outer_continuous P⟩
  retr_incl := functionSpaceRetrIncl P
  incl_retr_le := functionSpaceInclRetrLe P

end DomainTheory.ContinuousLattice
