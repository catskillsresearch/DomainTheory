/-ai
The identity combinator is the graph of the identity endomap of Pω. In Scott's notation it is λu. u, the largest retract.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- The identity combinator `I = λu. u`, the largest retract. -/
def Icomb : Pomega := graph (fun x => x)

end DomainTheory.DataTypesAsLattices
