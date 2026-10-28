module

public import DomainTheory.DataTypesAsLattices.Lambda.dcondSet
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Lambda.predSet
public import DomainTheory.DataTypesAsLattices.Lambda.dcondSet_more

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem dcondSet_same_ofNat (n : ℕ) (x : Pomega) :
    dcondSet (ofNat n) x x = x :=
  match n with
  | 0 => dcondSet.ofNat_zero x x
  | n + 1 => dcondSet.ofNat_succ n x x

end DomainTheory.DataTypesAsLattices
