module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic
public import DomainTheory.DataTypesAsLattices.Retracts.intR_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem intR_bot : funOf intR botElem = botElem := by
  rw [intR_app, dcondSet_bot]

end DomainTheory.DataTypesAsLattices
