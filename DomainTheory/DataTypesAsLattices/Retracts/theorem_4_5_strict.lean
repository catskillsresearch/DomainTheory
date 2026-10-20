module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices














































/-- **Scott 1976, Theorem 4.5 (i), strictness of sums.** The zero summand
is always selected on `⊥`. -/
theorem theorem_4_5_strict (a b : Pomega) :
    dcondSet botElem
      (pairSeq (ofNat 0) (funOf a botElem))
      (pairSeq (ofNat 1) (funOf b botElem)) = botElem :=
  dcondSet_bot _ _

end DomainTheory.DataTypesAsLattices
