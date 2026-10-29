module

public import DomainTheory.ContinuousLattice.FunctionSpaces.fix
public import DomainTheory.ContinuousLattice.FunctionSpaces.fix_le
public import DomainTheory.ContinuousLattice.FunctionSpaces.fix_eq
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

public import DomainTheory.ContinuousLattice.FunctionSpaces.ScottMap
@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y]

variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

namespace Proposition314

theorem fix_mono {f f' : ScottMap D D} (hff' : f ≤ f') : fix f ≤ fix f' :=
  fix_le (le_trans (ScottMap.le_def.mp hff' (fix f')) (le_of_eq (fix_eq f')))

end Proposition314

end DomainTheory.ContinuousLattice
