module

public import DomainTheory.ContinuousLattice.InverseLimits
public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import Mathlib.Topology.Homeomorph.Defs
import all Mathlib.Topology.Homeomorph.Defs
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.CLat
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.towerType
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.BasicInst5

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.ContinuousLattice

universe u

attribute [instance] CLat.str

@[simp] theorem towerType_zero (D₀ : CLat.{u}) : towerType D₀ 0 = D₀.carrier := rfl

end DomainTheory.ContinuousLattice
