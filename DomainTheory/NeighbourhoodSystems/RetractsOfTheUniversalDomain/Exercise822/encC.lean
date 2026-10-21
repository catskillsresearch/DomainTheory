/-ai
The completed encoding of a string is its doubled encoding followed by the two-bit marker whose bits are true and then false.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62

namespace Exercise822

/-- The "completed" encoding: `enc σ` followed by the two-bit marker `[true, false]`, which can
never arise as a doubled block `[b, b]`. -/
def encC (σ : Str) : Str := enc σ ++ [true, false]

end Exercise822

end DomainTheory.NeighbourhoodSystems
