module

public import DomainTheory.ContinuousLattice.FunctionSpaces.scottLambda
import DomainTheory.ContinuousLattice.FunctionSpaces.scottLambda_preservesDirectedSup
import DomainTheory.ContinuousLattice.ScottMaps.continuous_of_preservesDirectedSup

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

theorem proposition_3_5 :
    @Continuous (ScottMap (D × D') D'') (ScottMap D (ScottMap D' D''))
      scottTopologicalSpace scottTopologicalSpace scottLambda :=
  continuous_of_preservesDirectedSup scottLambda.preservesDirectedSup

end DomainTheory.ContinuousLattice
