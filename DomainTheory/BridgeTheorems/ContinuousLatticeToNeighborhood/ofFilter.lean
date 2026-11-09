module

public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.codes


@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.ContinuousLattice

open DomainTheory.NeighbourhoodSystems

open scoped DomainTheory.ContinuousLattice

namespace ContinuousLatticeToNeighborhood

variable {D : Type*} [CompleteLattice D]

noncomputable def ofFilter (f : Filter (D := D)) : D :=
  sSup (codes f)

end ContinuousLatticeToNeighborhood

end DomainTheory.BridgeTheorems
