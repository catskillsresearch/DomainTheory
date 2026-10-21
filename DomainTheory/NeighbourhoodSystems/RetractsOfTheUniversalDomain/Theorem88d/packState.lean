/-ai
The state packing of a remainder, a positive-list code, a negative-list code, and a U-code is the nested pair of those four numbers.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.eIdx_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.he0
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.hcover
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.genAtom_empty_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

section AtomCode

variable {E : NeighborhoodSystem α} (Q : ComputablePresentation E)

/-- Pack `(remK, posC, negC, uCode)` into a single state code. -/
def packState (remK posC negC uCode : ℕ) : ℕ := Nat.pair remK (Nat.pair posC (Nat.pair negC uCode))

end AtomCode

end DomainTheory.NeighbourhoodSystems
