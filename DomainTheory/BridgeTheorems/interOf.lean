module

public import Mathlib.Data.Finset.Fold
public import DomainTheory.BridgeTheorems.NbhdBasis

@[expose] public section

namespace DomainTheory.BridgeTheorems

namespace NbhdBasis

variable {ι α : Type*} [DecidableEq ι] (B : NbhdBasis ι α)

def interOf (u : Finset ι) : Set α :=
  u.fold (· ∩ ·) B.system.master B.nbhd

end NbhdBasis

end DomainTheory.BridgeTheorems
