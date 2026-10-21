/-ai
The principal up-set of y is the set of elements above y. This is the upper subbasic set of Scott's March 1972 correction.
ai-/
module

public import DomainTheory.ContinuousLattice.Specialization

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.ContinuousLattice

open Set Topology

variable {D D' : Type*} [CompleteLattice D] [CompleteLattice D']

/-- Upper subbasic set `{x | y ⊑ x}` (principal up-set) from the correction. -/
def scottPrincipalUpSet (y : D) : Set D :=
  Set.Ici y

end DomainTheory.ContinuousLattice
