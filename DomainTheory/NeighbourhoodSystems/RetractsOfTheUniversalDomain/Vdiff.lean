/-ai
The difference index of two indices is the canonical index of their raw difference code.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.VdiffRaw

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- The difference index: `canonIdx` of the raw difference code `VdiffRaw`. -/
def Vdiff (n m : ℕ) : ℕ := canonIdx (VdiffRaw n m)

end DomainTheory.NeighbourhoodSystems
