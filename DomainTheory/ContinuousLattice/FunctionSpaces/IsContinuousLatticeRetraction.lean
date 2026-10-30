module

public import DomainTheory.ContinuousLattice.FunctionSpaces.ScottMap

@[expose] public section

universe u v

namespace DomainTheory.ContinuousLattice

structure IsContinuousLatticeRetraction (D : Type u) (D' : Type v)
    [CompleteLattice D] [CompleteLattice D'] where
  incl : ScottMap D D'
  retr : ScottMap D' D
  retr_incl : ∀ d, retr (incl d) = d

end DomainTheory.ContinuousLattice
