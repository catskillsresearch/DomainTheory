module

public import DomainTheory.DataTypesAsLattices.Graph
public import DomainTheory.DataTypesAsLattices.FixedPoint.iterateBot

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, Theorem 1.4.** Least fixed point `fix(f) = ⋃_n fⁿ(∅)`. -/
def fix (f : Pomega → Pomega) : Pomega :=
  ⋃ n, iterateBot f n

end DomainTheory.DataTypesAsLattices
