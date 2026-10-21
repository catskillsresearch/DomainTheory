/-ai
The lower subbasic set determined by y is the set of elements that do not lie below y. This is the lower subbasic set of Scott's March 1972 correction.
ai-/
module

public import DomainTheory.ContinuousLattice.Specialization

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology

variable {D D' : Type*} [CompleteLattice D] [CompleteLattice D']

/-- Lower subbasic set `{x | x ⋢ y}` from Scott's March 1972 correction. -/
def scottLowerSubbasisSet (y : D) : Set D :=
  { x | ¬ x ≤ y }

end DomainTheory.ContinuousLattice
