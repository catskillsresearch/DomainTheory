module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.condSet_ofNat_zero
public import DomainTheory.DataTypesAsLattices.Functionality.condSet_ofNat_one
public import DomainTheory.DataTypesAsLattices.Functionality.seq4_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices
































theorem seq4_app_one (a b c d : Pomega) :
    funOf (seq4 a b c d) (ofNat 1) = b := by
  rw [seq4_app, condSet_ofNat_one, predSet_ofNat_succ, condSet_ofNat_zero]

end DomainTheory.DataTypesAsLattices
