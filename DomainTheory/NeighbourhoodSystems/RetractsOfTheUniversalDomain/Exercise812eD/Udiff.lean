/-ai
The difference index of two codes is the code-level difference of their canonical codes.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitV
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- The difference index: `diffCode` on canonicalized codes (`UX` re-canonicalizes on lookup, so no
further canonicalization is needed here — mirrors `Uinter`). -/
def Udiff (n m : ℕ) : ℕ := diffCode (canonCode n) (canonCode m)

end DomainTheory.NeighbourhoodSystems
