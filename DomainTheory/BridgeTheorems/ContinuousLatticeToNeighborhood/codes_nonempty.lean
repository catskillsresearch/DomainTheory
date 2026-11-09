module

public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.codes

public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.bot_mem_codes

@[expose] public section

namespace DomainTheory.BridgeTheorems

namespace ContinuousLatticeToNeighborhood

variable {D : Type*} [CompleteLattice D]

theorem codes_nonempty (f : Filter (D := D)) : (codes f).Nonempty :=
  ⟨⊥, bot_mem_codes f⟩

end ContinuousLatticeToNeighborhood

end DomainTheory.BridgeTheorems
