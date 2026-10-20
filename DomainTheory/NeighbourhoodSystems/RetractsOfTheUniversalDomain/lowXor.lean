module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- The low-bit XOR `(x ^^^ y) % 2`, in arithmetic `{0,1}`-valued form: the sum of the low bits,
mod `2`. -/
def lowXor (x y : ℕ) : ℕ := (x % 2 + y % 2) % 2

end DomainTheory.NeighbourhoodSystems
