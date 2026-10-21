/-ai
Scott 1976, Theorem 4.5 (i), strictness of sums. The doubly strict conditional on the bottom element, between the zero-tagged image of the bottom element under the first argument and the one-tagged image under the second, equals the bottom element. The zero summand is the one selected on the bottom element.

This is the bottom clause of the doubly strict conditional.
ai-/
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
