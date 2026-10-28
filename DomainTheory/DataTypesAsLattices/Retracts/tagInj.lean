module

public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Retracts.pairSeq

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def tagInj (i : ℕ) (x : Pomega) : Pomega := pairSeq (ofNat i) x

end DomainTheory.DataTypesAsLattices
