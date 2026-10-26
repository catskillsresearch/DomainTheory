module

public import DomainTheory.DataTypesAsLattices.Enumeration.barStep
public import DomainTheory.DataTypesAsLattices.FixedPoint.fix

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (3.15).** The bar combinator as a least fixed point. -/
def barComb : Pomega := fix barStep

end DomainTheory.DataTypesAsLattices
