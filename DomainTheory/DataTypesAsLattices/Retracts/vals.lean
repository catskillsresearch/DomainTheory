/-ai
The values of a set of fixed points of a map on Pω are the image of that set under the inclusion of the fixed-point subtype into Pω.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Fixpoints

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- Image of a set of fixed-point subtypes. -/
def Fixpoints.vals {f : Pomega → Pomega} (A : Set (Fixpoints f)) : Set Pomega :=
  Subtype.val '' A

end DomainTheory.DataTypesAsLattices
