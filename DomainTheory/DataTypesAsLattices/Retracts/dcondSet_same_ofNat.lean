module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices














































theorem dcondSet_same_ofNat (n : ℕ) (x : Pomega) :
    dcondSet (ofNat n) x x = x :=
  match n with
  | 0 => dcondSet_ofNat_zero x x
  | n + 1 => dcondSet_ofNat_succ n x x

end DomainTheory.DataTypesAsLattices
