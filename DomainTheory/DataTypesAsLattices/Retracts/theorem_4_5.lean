/-ai
Scott 1976, Theorem 4.5, the sum theorem, in its core form. The doubly strict conditional on the bottom element, with branches the zero-tagged image of the bottom element under the first summand and the one-tagged image under the second, equals the bottom element, and the bottom element is a retract.

The conditional equation is the strictness clause of the sum theorem, and the bottom element is a retract by the bottom retract lemma.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic
public import DomainTheory.DataTypesAsLattices.Retracts.theorem_4_5_strict

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

















































/-- **Scott 1976, Theorem 4.5 (The sum theorem), core.** -/
theorem theorem_4_5 :
    dcondSet botElem
        (pairSeq (ofNat 0) (funOf a botElem))
        (pairSeq (ofNat 1) (funOf b botElem)) = botElem ∧
      IsRetract botElem :=
  ⟨theorem_4_5_strict a b, bot_isRetract⟩

end DomainTheory.DataTypesAsLattices
