/-ai
The midpoint code of an index is the code of the rational midpoint of the pair formed by the minimum left endpoint and the maximum right endpoint of its canonical presenting list.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.listMinFstCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.listMaxSndCode

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- The midpoint code of `canonCode n`'s intrinsic `(min, max)` pair. -/
def splitU2MidCode (n : ℕ) : ℕ :=
  ratMidCode (Nat.pair (listMinFstCode (canonCode n)) (listMaxSndCode (canonCode n)))

end DomainTheory.NeighbourhoodSystems
