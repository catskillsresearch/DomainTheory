/-ai
An element of the successor level of the function-space tower may be applied as a map from the preceding level to itself. The coercion is the underlying map of that level.
ai-/
module

public import DomainTheory.ContinuousLattice.InverseLimits
public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import Mathlib.Topology.Homeomorph.Defs
import all Mathlib.Topology.Homeomorph.Defs
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.CLat
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.towerType
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.BasicInst5
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.towerType_zero
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.towerToMap

@[expose] public section

namespace DomainTheory.ContinuousLattice


attribute [instance] CLat.str

/-- Apply an element of `D_{n+1}` as a function `Dₙ → Dₙ` (definitional via `towerType_succ`). -/
instance towerCoeFun {D₀ : CLat.{u}} {n : ℕ} :
    CoeFun (towerType D₀ (n + 1)) (fun _ => towerType D₀ n → towerType D₀ n) where
  coe f := towerToMap f

end DomainTheory.ContinuousLattice
