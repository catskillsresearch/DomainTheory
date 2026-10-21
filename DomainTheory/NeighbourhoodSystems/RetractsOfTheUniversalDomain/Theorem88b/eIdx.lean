/-ai
The index swap sends 0 to the master index, sends the master index to 0, and fixes every other natural number. It moves the index of the master neighbourhood to 0 and leaves the rest of the enumeration in place.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtomDecidable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- **Swap `0` and `P.masterIdx`.** A primitive-recursive involution on `ℕ` re-pointing whichever
index `P.masterIdx` names `D`'s master neighbourhood to sit at index `0` instead, leaving every
other index fixed. -/
def eIdx (n : ℕ) : ℕ :=
  if n = 0 then P.masterIdx else if n = P.masterIdx then 0 else n

end DomainTheory.NeighbourhoodSystems
