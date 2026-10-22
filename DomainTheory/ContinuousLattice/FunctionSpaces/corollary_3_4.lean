module

public import DomainTheory.ContinuousLattice.FunctionSpaces.Basic
public import DomainTheory.ContinuousLattice.FunctionSpaces.corollary_3_4_eval_on_C
public import DomainTheory.ContinuousLattice.FunctionSpaces.scottFunctionTopology
public import Mathlib.Data.Set.Basic
public import Mathlib.Topology.Defs.Basic

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace


variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']


/-- **Scott 1972, Corollary 3.4 (fixed `x`).** Evaluation at fixed `x` is continuous on `[D → D']`
(with Scott topologies on `D` and `D'`); this is one half of the separate-continuity input to
joint continuity. -/
theorem corollary_3_4 (x : D) :
    @Continuous (ScottC D D') D'
      (@scottFunctionTopology D D' scottTopologicalSpace scottTopologicalSpace)
      scottTopologicalSpace (fun f : ScottC D D' => f x) :=
  corollary_3_4_eval_on_C (D := D) (D' := D') x

end DomainTheory.ContinuousLattice
