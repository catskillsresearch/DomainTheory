/-ai
Each level of the function-space tower carries the complete-lattice structure of the bundled lattice at that level.
ai-/
module

public import DomainTheory.ContinuousLattice.InverseLimits
public import Mathlib.Order.Hom.Basic
public import Mathlib.Topology.Homeomorph.Defs
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.CLat
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.towerCLat
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.towerType

@[expose] public section

namespace DomainTheory.ContinuousLattice


attribute [instance] CLat.str

noncomputable instance towerCompleteLattice (D₀ : CLat.{u}) (n : ℕ) :
    CompleteLattice (towerType D₀ n) := (towerCLat D₀ n).str

end DomainTheory.ContinuousLattice
