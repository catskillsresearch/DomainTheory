/-ai
Every Scott map is a monotone function of its underlying map.

Scott continuity of the underlying function is equivalent to preservation of directed suprema, and a map that preserves directed suprema is monotone.
ai-/
module

public import DomainTheory.ContinuousLattice.FunctionSpaces.ScottMap
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
