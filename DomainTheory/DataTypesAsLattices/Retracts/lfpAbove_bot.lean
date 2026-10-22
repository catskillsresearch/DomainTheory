module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic
public import DomainTheory.DataTypesAsLattices.Retracts.iterateFrom_bot

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem lfpAbove_bot (f : Pomega → Pomega) : lfpAbove f botElem = fix f := by
  simp [lfpAbove, fix, iterateFrom_bot]

end DomainTheory.DataTypesAsLattices
