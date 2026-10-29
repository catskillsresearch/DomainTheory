module

public import DomainTheory.ContinuousLattice.FunctionSpaces.Basic
public import DomainTheory.ContinuousLattice.FunctionSpaces.ScottFunctionTopology
import DomainTheory.ContinuousLattice.ScottMaps.proposition_2_6
import DomainTheory.ContinuousLattice.FunctionSpaces.sSup_apply
import DomainTheory.ContinuousLattice.ScottMaps.proposition_2_5
import DomainTheory.ContinuousLattice.ScottMaps.continuous_of_preservesDirectedSup

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

namespace corollary_3_4

theorem eval_on_C (x : D) :
    @Continuous (ScottC D D') D'
      (@scottFunctionTopology D D' scottTopologicalSpace scottTopologicalSpace)
      scottTopologicalSpace (fun f : ScottC D D' => f x) :=
  continuous_def.2 fun _U hU =>
    scottFunctionTopology.subbasis_isOpen_scott (D := D) (D' := D') (x := x) hU

theorem preservesDirectedSup :
    PreservesDirectedSup (fun p : ScottMap D D' × D => (p.1 : D → D') p.2) := by
  rw [proposition_2_6]
  constructor
  · intro y S hS hSdir
    show ((sSup S : ScottMap D D') : D → D') y
        = sSup ((fun x : ScottMap D D' => (x : D → D') y) '' S)
    rw [ScottMap.sSup_apply]
  · intro x
    exact (proposition_2_5 _).mp x.continuous

theorem jointly_continuous :
    @Continuous (ScottMap D D' × D) D' scottTopologicalSpace scottTopologicalSpace
      (fun p : ScottMap D D' × D => (p.1 : D → D') p.2) :=
  continuous_of_preservesDirectedSup preservesDirectedSup

end corollary_3_4

theorem corollary_3_4 (x : D) :
    @Continuous (ScottC D D') D'
      (@scottFunctionTopology D D' scottTopologicalSpace scottTopologicalSpace)
      scottTopologicalSpace (fun f : ScottC D D' => f x) :=
  corollary_3_4.eval_on_C x

end DomainTheory.ContinuousLattice
