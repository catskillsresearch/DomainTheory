module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.comp
public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst36

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem bot_isRetract : Retract botElem := by
  constructor
  unfold comp botElem
  ext p
  simp [graph, funOf]

end DomainTheory.DataTypesAsLattices
