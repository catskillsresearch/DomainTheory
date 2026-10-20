module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62

namespace Exercise822

/-- Doubles every bit of a string: `enc [] = []`, `enc (b :: σ) = b :: b :: enc σ`. -/
def enc : Str → Str
  | [] => []
  | b :: σ => b :: b :: enc σ

end Exercise822

end DomainTheory.NeighbourhoodSystems
