/-ai
The least upper bound of the iterates of a map above the bottom element is the least fixed point of the map.

Unfold both sides and use that iteration from the bottom element agrees with the Kleene approximants.
ai-/
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
