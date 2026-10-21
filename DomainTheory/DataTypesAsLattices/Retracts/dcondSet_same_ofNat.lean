/-ai
The doubly strict conditional of the numeral n on a repeated argument x equals x.

The case of zero is the conditional on the numeral zero. The successor case is the conditional on a positive numeral.
ai-/
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
