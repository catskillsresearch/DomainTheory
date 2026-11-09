module

public import DomainTheory.BridgeTheorems.interOf

@[expose] public section

namespace DomainTheory.BridgeTheorems

namespace NbhdBasis

variable {ι α : Type*} [DecidableEq ι] (B : NbhdBasis ι α)

@[simp] theorem interOf_empty : B.interOf (∅ : Finset ι) = B.system.master := rfl

end NbhdBasis

end DomainTheory.BridgeTheorems
