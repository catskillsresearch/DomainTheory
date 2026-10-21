/-ai
Scott 1976, Theorem 4.4, the product theorem, in its core form. A pair, regarded as a function, projects to its two components, and the bottom element is a retract.

The projection equations are the pairing form of clause (ii), and the bottom element is a retract by the bottom retract lemma.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic
public import DomainTheory.DataTypesAsLattices.Retracts.theorem_4_4_ii

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, Theorem 4.4 (The product theorem), core.** -/
theorem theorem_4_4 :
    (∀ x y, funOf (pairSeq x y) (ofNat 0) = x ∧
      funOf (pairSeq x y) (ofNat 1) = y) ∧
      IsRetract botElem :=
  ⟨fun x y => theorem_4_4_ii x y, bot_isRetract⟩

end DomainTheory.DataTypesAsLattices
