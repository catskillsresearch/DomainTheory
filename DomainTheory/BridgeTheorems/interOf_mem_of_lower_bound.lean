module

public import DomainTheory.BridgeTheorems.interOf
import DomainTheory.BridgeTheorems.interOf_empty
import DomainTheory.BridgeTheorems.interOf_insert

@[expose] public section

namespace DomainTheory.BridgeTheorems

namespace NbhdBasis

variable {ι α : Type*} [DecidableEq ι] (B : NbhdBasis ι α)

theorem interOf_mem_of_lower_bound {u : Finset ι} {Z : Set α}
    (hZ : B.system.mem Z) (hsub : Z ⊆ B.interOf u) : B.system.mem (B.interOf u) := by
  induction u using Finset.induction with
  | empty =>
    simpa [interOf_empty] using B.system.master_mem
  | insert a s ha ih =>
    rw [B.interOf_insert ha] at hsub ⊢
    have hs : B.system.mem (B.interOf s) := ih (hsub.trans Set.inter_subset_right)
    exact B.system.inter_mem (B.nbhd_mem a) hs hZ hsub

end NbhdBasis

end DomainTheory.BridgeTheorems
