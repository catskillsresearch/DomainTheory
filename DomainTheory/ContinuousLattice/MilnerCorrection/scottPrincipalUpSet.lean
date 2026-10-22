module

public import DomainTheory.ContinuousLattice.Specialization

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology

variable {D D' : Type*} [CompleteLattice D] [CompleteLattice D']

/-- Upper subbasic set `{x | y ⊑ x}` (principal up-set) from the correction. -/
def scottPrincipalUpSet (y : D) : Set D :=
  Set.Ici y

end DomainTheory.ContinuousLattice
