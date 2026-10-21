/-ai
The empty set is a retract.

Unfolding the retract equation, composition, and the empty set, extensionality together with the definitions of the graph and of application gives the equality.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.comp
public import DomainTheory.DataTypesAsLattices.Retracts.IsRetract
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst36

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem bot_isRetract : IsRetract botElem := by
  unfold IsRetract comp botElem
  ext p
  simp [graph, funOf]

end DomainTheory.DataTypesAsLattices
