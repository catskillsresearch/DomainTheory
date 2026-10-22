/-ai
The n-th summand of the projection j_∞ is the Scott map from [D_∞ → D_∞] to D_∞ sending f to the level-(n+1) embedding of the conjugate j_{∞n} ∘ f ∘ i_{n∞}. It is conjugation by the pair (j_{∞n}, i_{n∞}), with values in D_{n+1}, followed by the embedding of level n+1.
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
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.iInfTerm_apply

@[expose] public section

namespace DomainTheory.ContinuousLattice


attribute [instance] CLat.str

section LimitMaps

variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))

/-- The `n`-th summand of `j_∞`: the Scott map `f ↦ i_{(n+1)∞}(j_{∞n} ∘ f ∘ i_{n∞})`. As a map
`[D_∞ → D_∞] → D_∞` it is conjugation by `(j_{∞n}, i_{n∞})` (landing in `D_{n+1}`) followed by the
embedding `i_{(n+1)∞}`. -/
noncomputable def jInfTerm (n : ℕ) : ScottMap (DInfFn D₀ j₀) (DInf D₀ j₀) :=
  (embInf (towerType D₀) (towerProj D₀ j₀) (n + 1)).comp
    (conjMap (projInf (towerType D₀) (towerProj D₀ j₀) n)
             (embInf (towerType D₀) (towerProj D₀ j₀) n))

end LimitMaps

end DomainTheory.ContinuousLattice
