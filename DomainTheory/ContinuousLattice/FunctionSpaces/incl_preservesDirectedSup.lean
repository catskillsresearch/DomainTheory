module

public import DomainTheory.ContinuousLattice.ScottMaps.PreservesDirectedSup
public import DomainTheory.ContinuousLattice.FunctionSpaces.IsContinuousLatticeRetraction
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

namespace IsContinuousLatticeRetraction

theorem incl_preservesDirectedSup (R : IsContinuousLatticeRetraction D D') :
    PreservesDirectedSup (R.incl : D → D') :=
  fun _ hS hSdir => R.incl.preservesDirectedSup_coe _ hS hSdir

end IsContinuousLatticeRetraction
end DomainTheory.ContinuousLattice
