module

public import DomainTheory.BridgeTheorems.ConjScottMap

@[expose] public section

namespace DomainTheory.BridgeTheorems

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable {D E : Type*} [CompleteLattice D] [CompleteLattice E]

namespace ConjScottMap

variable {D' E' : Type*} [PartialOrder D'] [PartialOrder E']

variable (ιD : D ≃o D') (ιE : E ≃o E')

theorem ext {f g : ConjScottMap ιD ιE} (h : f.scott = g.scott) : f = g := by
  cases f; cases g; congr

end ConjScottMap

end DomainTheory.BridgeTheorems
