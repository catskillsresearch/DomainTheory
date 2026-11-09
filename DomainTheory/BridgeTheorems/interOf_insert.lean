module

public import DomainTheory.BridgeTheorems.interOf

@[expose] public section

namespace DomainTheory.BridgeTheorems



namespace NbhdBasis

variable {ι α : Type*} [DecidableEq ι] (B : NbhdBasis ι α)

theorem interOf_insert {a : ι} {s : Finset ι} (ha : a ∉ s) :
    B.interOf (insert a s) = B.nbhd a ∩ B.interOf s :=
  Finset.fold_insert (op := (· ∩ ·)) ha

end NbhdBasis

end DomainTheory.BridgeTheorems
