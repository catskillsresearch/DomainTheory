/-ai
Scott 1976, (4.39). The lambda functor sends a retract z to the sum of the integer retract with the function space of z into itself.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR
public import DomainTheory.DataTypesAsLattices.Retracts.plusR
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst36
public import DomainTheory.DataTypesAsLattices.Retracts.intR
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst55

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (4.39).** `lamb = int ⊕ (lamb ∘→ lamb)`. -/
def lambF (z : Pomega) : Pomega := plusR intR (arrowR z z)

end DomainTheory.DataTypesAsLattices
