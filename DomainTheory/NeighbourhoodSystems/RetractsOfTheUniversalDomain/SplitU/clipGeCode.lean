/-ai
clipGeCode clips a rational-pair code to the closed ray from the decoded midpoint. On a packed pair of the midpoint code and the pair code, it replaces the left endpoint by the maximum of that endpoint and the midpoint, and leaves the right endpoint unchanged.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- Clip a rational-pair code `e` to `[decodeRat m, ∞)`, given `t = pair m e`. -/
def clipGeCode (t : ℕ) : ℕ :=
  Nat.pair (ratMaxCode (Nat.pair t.unpair.2.unpair.1 t.unpair.1)) t.unpair.2.unpair.2

end DomainTheory.NeighbourhoodSystems
