module

public import DomainTheory.ContinuousLattice.WayBelow.WayBelow

@[expose] public section

namespace DomainTheory.ContinuousLattice

universe u

variable {D : Type u} [CompleteLattice D]

@[inherit_doc] scoped infix:50 " ≪ " => WayBelow

end DomainTheory.ContinuousLattice
