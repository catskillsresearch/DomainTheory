/-ai
Scott 1976, Theorem 4.4 (i). The product of two strict maps is strict.

The product applied to bottom is the sequence pair of the two applications at bottom. Strictness makes both applications bottom, and the sequence pair of two bottoms is bottom.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.tensorR_app
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_bot

@[expose] public section


namespace DomainTheory.DataTypesAsLattices















/-- **Scott 1976, Theorem 4.4 (i), strictness.** -/
theorem tensorR_isStrict {a b : Pomega} (ha : IsStrict a) (hb : IsStrict b) :
    IsStrict (tensorR a b) := by
  change funOf (tensorR a b) botElem = botElem
  rw [tensorR_app, funOf_bot, funOf_bot, ha, hb, pairSeq_bot]

end DomainTheory.DataTypesAsLattices
