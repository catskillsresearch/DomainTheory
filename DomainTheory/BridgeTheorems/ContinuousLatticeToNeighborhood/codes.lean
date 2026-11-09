module

public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.Filter

@[expose] public section

namespace DomainTheory.BridgeTheorems

namespace ContinuousLatticeToNeighborhood

variable {D : Type*} [CompleteLattice D]

def codes (f : Filter (D := D)) : Set D :=
  {a : D | f.mem (wayBelowUp a)}

end ContinuousLatticeToNeighborhood

end DomainTheory.BridgeTheorems
