
module

public import DomainTheory.DataTypesAsLattices.Retracts.tensorR
public import DomainTheory.DataTypesAsLattices.Retracts.IsStrict
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.tensorR_app
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_bot
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, Theorem 4.4 (i), strictness.** -/
theorem tensorR_isStrict {a b : Pomega} (ha : IsStrict a) (hb : IsStrict b) :
    IsStrict (tensorR a b) := by
  change funOf (tensorR a b) botElem = botElem
  rw [tensorR_app, funOf.bot, funOf.bot, ha, hb, pairSeq_bot]

end DomainTheory.DataTypesAsLattices
