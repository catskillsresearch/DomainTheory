/-ai
Scott's equation (4.30) defines the summand tag to be the same combinator as the first projection.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (4.30).** Tag of a summand; same combinator as `fst`. -/
def whichC : Pomega := fstC

end DomainTheory.DataTypesAsLattices
