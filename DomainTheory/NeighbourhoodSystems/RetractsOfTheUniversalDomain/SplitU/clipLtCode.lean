/-ai
clipLtCode clips a rational-pair code to the open ray below the decoded midpoint. On a packed pair of the midpoint code and the pair code, it leaves the left endpoint and replaces the right endpoint by the minimum of that endpoint and the midpoint.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- Clip a rational-pair code `e` to `(-∞, decodeRat m)`, given `t = pair m e`. -/
def clipLtCode (t : ℕ) : ℕ :=
  Nat.pair t.unpair.2.unpair.1 (ratMinCode (Nat.pair t.unpair.2.unpair.2 t.unpair.1))

end DomainTheory.NeighbourhoodSystems
