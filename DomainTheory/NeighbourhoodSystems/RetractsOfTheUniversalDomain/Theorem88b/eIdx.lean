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
