/-ai
Every value of the enumeration of V is a neighbourhood of V.

It is the level set of the level and mask of the canonicalized code, and that level set
is nonempty.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.canonIdx
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.levelSet_canonIdx_nonempty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.VX

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- Every `VX n` is a genuine `V`-neighbourhood. -/
theorem V_mem_VX (c : ℕ) : V.mem (VX c) :=
  ⟨(canonIdx c).unpair.1, (canonIdx c).unpair.2, rfl, levelSet_canonIdx_nonempty c⟩

end DomainTheory.NeighbourhoodSystems
