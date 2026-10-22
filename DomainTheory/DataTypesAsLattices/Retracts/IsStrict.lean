module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst36

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- Strictness: `a(⊥) = ⊥`, equivalently `⊥ ⊑ a` for retracts. -/
def IsStrict (a : Pomega) : Prop :=
  funOf a botElem = botElem

end DomainTheory.DataTypesAsLattices
