
module

public import DomainTheory.DataTypesAsLattices.Retracts.seq4
public import DomainTheory.DataTypesAsLattices.Lambda.predSet
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Lambda.condSet
public import DomainTheory.DataTypesAsLattices.Functionality.seq4_app
public import DomainTheory.DataTypesAsLattices.Lambda.predSet_more

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem seq4_app_one (a b c d : Pomega) :
    funOf (seq4 a b c d) (ofNat 1) = b := by
  rw [seq4_app, condSet.ofNat_one, predSet.ofNat_succ, condSet.ofNat_zero]

end DomainTheory.DataTypesAsLattices
