module

public import DomainTheory.ContinuousLattice.FunctionSpaces.ScottFunctionTopology
public import Mathlib.Order.BourbakiWitt
public import DomainTheory.ContinuousLattice.ScottMaps.proposition_2_5
public import DomainTheory.ContinuousLattice.ScottMaps.preservesDirectedSup_monotone

@[expose] public section

namespace DomainTheory.ContinuousLattice

variable {D D' : Type*} [CompleteLattice D] [CompleteLattice D']

namespace ScottMap

theorem monotone (f : ScottMap D D') : Monotone (f : D → D') :=
  preservesDirectedSup_monotone ((proposition_2_5 (Subtype.val f)).mp f.property)

end ScottMap

end DomainTheory.ContinuousLattice
