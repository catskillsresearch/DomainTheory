/-ai
The n-th summand of the embedding i_∞ is the Scott map from D_∞ to [D_∞ → D_∞] sending x to i_{n∞} ∘ x_{n+1} ∘ j_{∞n}, where x_{n+1} is the (n+1)-st component of x. It is the composite of the component projection onto level n+1 with conjugation by the pair (i_{n∞}, j_{∞n}).
ai-/
module

public import DomainTheory.ContinuousLattice.InverseLimits
public import Mathlib.Order.Hom.Basic
public import Mathlib.Topology.Homeomorph.Defs
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.CLat
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.towerType
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.BasicInst5
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.towerType_zero
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.BasicInst8
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.towerToMap_coe
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.conjMap
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.conjMap_apply
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.towerProj
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.DInf
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.DInfFn

@[expose] public section

namespace DomainTheory.ContinuousLattice


attribute [instance] CLat.str

section LimitMaps

variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))

/-- The `n`-th summand of `i_∞`: the Scott map `x ↦ i_{n∞} ∘ x_{n+1} ∘ j_{∞n}`, where `x_{n+1}` is
the `(n+1)`-st component of `x ∈ D_∞`. As a map `D_∞ → [D_∞ → D_∞]` it is the composite of the
component projection `j_{∞(n+1)}` with conjugation by `(i_{n∞}, j_{∞n})`. -/
noncomputable def iInfTerm (n : ℕ) : ScottMap (DInf D₀ j₀) (DInfFn D₀ j₀) :=
  (conjMap (embInf (towerType D₀) (towerProj D₀ j₀) n)
           (projInf (towerType D₀) (towerProj D₀ j₀) n)).comp
    (projInf (towerType D₀) (towerProj D₀ j₀) (n + 1))

end LimitMaps

end DomainTheory.ContinuousLattice
