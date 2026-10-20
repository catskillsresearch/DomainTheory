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
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.DInf
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.DInfFn
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.iInfTerm_apply
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.jInfTerm
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.jInfTerm_apply

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.ContinuousLattice

universe u

attribute [instance] CLat.str

section LimitMaps

variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))

/-- **Scott 1972, §4 (Theorem 4.4).** The projection `j_∞ : [D_∞ → D_∞] → D_∞`,
`j_∞(f) = ⨆ₙ i_{(n+1)∞}(j_{∞n} ∘ f ∘ i_{n∞})`. Scott-continuous as a supremum of the Scott maps
`jInfTerm n`. -/
noncomputable def projInfInf : ScottMap (DInfFn D₀ j₀) (DInf D₀ j₀) :=
  ⨆ n, jInfTerm D₀ j₀ n

end LimitMaps

end DomainTheory.ContinuousLattice
