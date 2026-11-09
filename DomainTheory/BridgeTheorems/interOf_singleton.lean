module

public import DomainTheory.BridgeTheorems.interOf
import DomainTheory.BridgeTheorems.nbhd_subset_master

@[expose] public section

namespace DomainTheory.BridgeTheorems



namespace NbhdBasis

variable {ι α : Type*} [DecidableEq ι] (B : NbhdBasis ι α)

theorem interOf_singleton (a : ι) : B.interOf ({a} : Finset ι) = B.nbhd a := by
  simp [interOf, Finset.fold_singleton, Set.inter_eq_left.mpr (B.nbhd_subset_master a)]

end NbhdBasis

end DomainTheory.BridgeTheorems
