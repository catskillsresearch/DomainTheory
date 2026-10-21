/-ai
The and-not of a and b is the iterative exclusive disjunction of a with the iterative conjunction of a and b, which clears from a the bits set in b.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.myXor

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- `a` with `b`'s bits cleared: `a ^^^ (a &&& b)` (`testBit_xor_and_self`), computed via `myXor`
composed with the already-`Pass` `myLand`. -/
def myAndNot (a b : ℕ) : ℕ := myXor a (myLand a b)

end DomainTheory.NeighbourhoodSystems
