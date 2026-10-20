module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- Clip a rational-pair code `e` to `(-∞, decodeRat m)`, given `t = pair m e`. -/
def clipLtCode (t : ℕ) : ℕ :=
  Nat.pair t.unpair.2.unpair.1 (ratMinCode (Nat.pair t.unpair.2.unpair.2 t.unpair.1))

end DomainTheory.NeighbourhoodSystems
